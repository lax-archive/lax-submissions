import Lax457868Proofs.FlatTraceLaw
import Lax457868Proofs.ClassChoiceTransport
import Lax457868Proofs.InitialSamplerAttempt
import Lax457868Proofs.InitialSamplerChoice
import Lax457868Proofs.SamplerInitialRetries
import Lax457868Proofs.SourceTapePrefix

/-!
Flat-tape counting at the actual initial-attempt boundary. The first draw
stream determines the sample, hence the class sizes of the second stream.
The suffix following each stopped prefix remains available to the next call.
-/

namespace Lax457868Proofs.InitialFlatLaw

open Lax457868Proofs.FlatTraceLaw
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.SequentialDraws
open Lax457868Proofs.StoppingPrefix
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.ClassChoiceTransport
open Lax457868Proofs.EnumeratedDraws
open Lax457868Proofs.SamplerInitialProbability
open Lax457868Proofs.SamplerInitialExpectation
open Lax457868Proofs.SamplerInitialRetries
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.InitialSamplerChoice
open Lax457868Proofs.InitialSamplerAttempt
open Lax457868Proofs.InitialDrawSampleSource
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixMath

/-- A prescribed stopped path followed by an arbitrary event on precisely
the bits that remain after its actual consumed prefix. -/
def TerminalFlatEvent (size : ℕ → ℕ) (t : ℕ) (start : ℕ → ℕ)
    (d r : ℕ) (values attempts : List ℕ)
    (P : List Bool → Prop) (bits : List Bool) : Prop :=
  FlatClassSuccess size t start d r bits values attempts ∧
    P (bits.drop (consumedBits size d attempts))

private lemma firstStep_inv (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) {d r : ℕ} {bits : List Bool}
    {values attempts : List ℕ}
    (hflat : FlatClassSuccess size t start d (r + 1) bits values attempts) :
    ∃ (v : ℕ) (j : Fin (size d)) (pre : BitTape (size d) (v + 1))
      (rest : List Bool) (xs us : List ℕ),
      values = (start d + j.val) :: xs ∧ attempts = (v + 1) :: us ∧
      bits = tapeBits pre ++ rest ∧
      stoppedEvent (size d) (by have := j.isLt; omega) (v + 1) (v + 1) j pre ∧
      FlatClassSuccess size t start (d + 1) r rest xs us := by
  cases hflat with
  | step j pre rest hm hu hp hnext =>
      exact ⟨_, j, pre, rest, _, _, rfl, rfl, rfl, hp, hnext⟩

private lemma firstStep_iff (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r v : ℕ) (i : Fin (size d))
    (values attempts : List ℕ) (bits : List Bool)
    (hm : 0 < size d) (hu : v + 1 ≤ t) :
    FlatClassSuccess size t start d (r + 1) bits
      ((start d + i.val) :: values) ((v + 1) :: attempts) ↔
    stoppedFlatEvent (size d) hm v i
      (fun rest => FlatClassSuccess size t start (d + 1) r rest values attempts)
      bits := by
  constructor
  · intro hflat
    obtain ⟨w, j, pre, rest, xs, us, hvalues, hattempts, hbits, hp, hnext⟩ :=
      firstStep_inv size t start hflat
    have hheads := (List.cons.inj hvalues).1
    have htails := (List.cons.inj hvalues).2
    have huheads := (List.cons.inj hattempts).1
    have hutails := (List.cons.inj hattempts).2
    have hj : j = i := Fin.ext (Nat.add_left_cancel hheads).symm
    have hw : w = v := by omega
    subst j
    subst w
    subst xs
    subst us
    exact ⟨pre, hp, rest, hbits, hnext⟩
  · rintro ⟨pre, hp, rest, heq, hnext⟩
    rw [heq]
    exact FlatClassSuccess.step i pre rest hm hu hp hnext

/-- Exact factorization with a sample-dependent terminal event. This is the
stopped-prefix law needed when the sample drawn by the first stream decides
which representative classes the suffix will use. -/
lemma card_terminalFlatEvent (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {values attempts : List ℕ},
      (hpath : ValidPath size t start d r values attempts) →
      (N : ℕ) → (hbudget : bitBudget size t d r ≤ N) →
      (P : List Bool → Prop) →
      Nat.card {bits : List Bool // bits.length = N ∧
        TerminalFlatEvent size t start d r values attempts P bits} =
        stoppedWeight size d attempts *
          Nat.card {rest : List Bool //
            rest.length = N - consumedBits size d attempts ∧ P rest} := by
  intro d r values attempts hpath N hbudget P
  induction hpath generalizing N with
  | done d =>
      let e : {bits : List Bool // bits.length = N ∧
          TerminalFlatEvent size t start d 0 [] [] P bits} ≃
          {rest : List Bool // rest.length = N ∧ P rest} := {
        toFun := fun bits => ⟨bits.1, bits.2.1, by
          simpa [TerminalFlatEvent, consumedBits] using bits.2.2.2⟩
        invFun := fun rest => ⟨rest.1, rest.2.1,
          FlatClassSuccess.done d rest.1, by
            simpa [consumedBits] using rest.2.2⟩
        left_inv := by intro bits; apply Subtype.ext; rfl
        right_inv := by intro rest; apply Subtype.ext; rfl
      }
      rw [Nat.card_congr e]
      simp [stoppedWeight, consumedBits]
  | @step d r v i values attempts hm hu hnext ih =>
      let L := Nat.clog 2 (size d)
      change t * L + bitBudget size t (d + 1) r ≤ N at hbudget
      have hfirst : (v + 1) * L ≤ N := by
        have hmul : (v + 1) * L ≤ t * L := Nat.mul_le_mul_right L hu
        omega
      have htail : bitBudget size t (d + 1) r ≤ N - (v + 1) * L := by
        have hmul : (v + 1) * L ≤ t * L := Nat.mul_le_mul_right L hu
        omega
      let Q : List Bool → Prop := fun rest =>
        TerminalFlatEvent size t start (d + 1) r values attempts P rest
      have hdrop (pre : BitTape (size d) (v + 1)) (rest : List Bool) :
          (tapeBits pre ++ rest).drop
            ((v + 1) * L + consumedBits size (d + 1) attempts) =
          rest.drop (consumedBits size (d + 1) attempts) := by
        rw [← List.drop_drop]
        simp [tapeBits_length, L]
      have hchar (bits : List Bool) :
          TerminalFlatEvent size t start d (r + 1)
            ((start d + i.val) :: values) ((v + 1) :: attempts) P bits ↔
          stoppedFlatEvent (size d) hm v i Q bits := by
        constructor
        · rintro ⟨hflat, hP⟩
          obtain ⟨pre, hp, rest, hbits, hnextFlat⟩ :=
            (firstStep_iff size t start d r v i values attempts bits hm hu).mp hflat
          refine ⟨pre, hp, rest, hbits, hnextFlat, ?_⟩
          rw [hbits] at hP
          simpa [Q, TerminalFlatEvent, consumedBits, L, hdrop] using hP
        · rintro ⟨pre, hp, rest, hbits, hnextFlat, hP⟩
          constructor
          · exact (firstStep_iff size t start d r v i values attempts bits hm hu).mpr
              ⟨pre, hp, rest, hbits, hnextFlat⟩
          · rw [hbits]
            simpa [Q, TerminalFlatEvent, consumedBits, L, hdrop] using hP
      have hcard : Nat.card {bits : List Bool // bits.length = N ∧
          TerminalFlatEvent size t start d (r + 1)
            ((start d + i.val) :: values) ((v + 1) :: attempts) P bits} =
          Nat.card {bits : List Bool // bits.length = N ∧
            stoppedFlatEvent (size d) hm v i Q bits} := by
        let e : {bits : List Bool // bits.length = N ∧
            TerminalFlatEvent size t start d (r + 1)
              ((start d + i.val) :: values) ((v + 1) :: attempts) P bits} ≃
            {bits : List Bool // bits.length = N ∧
              stoppedFlatEvent (size d) hm v i Q bits} := {
          toFun := fun bits => ⟨bits.1, bits.2.1, (hchar bits.1).mp bits.2.2⟩
          invFun := fun bits => ⟨bits.1, bits.2.1, (hchar bits.1).mpr bits.2.2⟩
          left_inv := by intro bits; apply Subtype.ext; rfl
          right_inv := by intro bits; apply Subtype.ext; rfl
        }
        exact Nat.card_congr e
      rw [hcard, card_stoppedFlatEvent (size d) hm v N i Q hfirst]
      rw [ih (N - (v + 1) * L) htail]
      simp [stoppedWeight, consumedBits, Nat.sub_sub, L, mul_assoc]

/-- The actual initial `DrawTrace` is the constant-width case of the actual
flat `ClassTrace`, including the exact number of bits read. This preserves the
unread part of each capped call for the next draw. -/
lemma drawTrace_to_classTrace (m : ℕ) (hm : 0 < m) (t : ℕ) :
    ∀ (d : ℕ) {r : ℕ}
      {blocks : List (Fin (Nat.clog 2 m) → Bool)}
      {values : List (Fin m)} {used : ℕ} {failed : Bool},
      DrawTrace m hm t r blocks values used failed →
      ∃ charge, ClassTrace (fun _ => m) t (fun _ => 0) d r
        (blocks.flatMap List.ofFn) (values.map Fin.val)
        (used * Nat.clog 2 m) charge failed
  | d, _, _, _, _, _, .done blocks =>
      ⟨0, by simpa using
        (ClassTrace.done d (blocks.flatMap List.ofFn) :
          ClassTrace (fun _ => m) t (fun _ => 0) d 0
            (blocks.flatMap List.ofFn) [] 0 0 false)⟩
  | d, _, _, _, _, _, .failed tape tail u hsel => by
      refine ⟨(15 * Nat.clog 2 m + 30) * u +
        12 * Nat.clog 2 m + 61, ?_⟩
      simpa [tapeBits, List.flatMap_append] using
        (ClassTrace.failed tape (tail.flatMap List.ofFn) u hm hsel :
          ClassTrace (fun _ => m) t (fun _ => 0) d _ _ _ _ _ true)
  | d, _, _, _, _, _, .accepted (r := r) (values := values)
      (used := used) (failed := failed) tape tail i u hsel hnext => by
      obtain ⟨charge, hclassNext⟩ :=
        drawTrace_to_classTrace m hm t (d + 1) hnext
      have hnextBits :
          (((List.ofFn tape).drop u ++ tail).flatMap List.ofFn) =
            (tapeBits tape).drop (u * Nat.clog 2 m) ++
              tail.flatMap List.ofFn := by
        simp only [List.flatMap_append]
        rw [tapeBits_drop]
      have hclassNext' : ClassTrace (fun _ => m) t (fun _ => 0) (d + 1) r
          ((tapeBits tape).drop (u * Nat.clog 2 m) ++ tail.flatMap List.ofFn)
          (values.map Fin.val) (used * Nat.clog 2 m) charge failed := by
        simpa only [hnextBits] using hclassNext
      refine ⟨(15 * Nat.clog 2 m + 30) * u +
        12 * Nat.clog 2 m + 61 + charge, ?_⟩
      have hclass := ClassTrace.accepted (size := fun _ => m) (t := t)
        (start := fun _ => 0) (d := d) (r := r) tape
        (tail.flatMap List.ofFn) i u hm hsel hclassNext'
      simpa only [tapeBits, List.flatMap_append, List.map_cons, zero_add,
        Nat.add_mul] using hclass

private lemma card_flatPredicate (N : ℕ) (P : List Bool → Prop)
    [DecidablePred (fun tape : FlatTape N => P (flatBits tape))] :
    Nat.card {bits : List Bool // bits.length = N ∧ P bits} =
      (Finset.univ.filter fun tape : FlatTape N => P (flatBits tape)).card := by
  classical
  let e : {tape : FlatTape N // P (flatBits tape)} ≃
      {bits : List Bool // bits.length = N ∧ P bits} := {
    toFun := fun tape => ⟨flatBits tape.1, flatBits_length tape.1, tape.2⟩
    invFun := fun bits => ⟨(flatBitsEquiv N).symm ⟨bits.1, bits.2.1⟩,
      by
        have heq : flatBits ((flatBitsEquiv N).symm ⟨bits.1, bits.2.1⟩) = bits.1 :=
          congrArg Subtype.val
            ((flatBitsEquiv N).apply_symm_apply ⟨bits.1, bits.2.1⟩)
        simpa only [heq] using bits.2.2⟩
    left_inv := by
      intro tape
      apply Subtype.ext
      exact (flatBitsEquiv N).left_inv tape.1
    right_inv := by
      intro bits
      apply Subtype.ext
      change flatBits ((flatBitsEquiv N).symm ⟨bits.1, bits.2.1⟩) = bits.1
      exact congrArg Subtype.val
        ((flatBitsEquiv N).right_inv ⟨bits.1, bits.2.1⟩)
  }
  symm
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype]

/-- The sample-determining stopped draw prefix and the actual representative
trace have an exact joint fiber count for every fixed stopping vector. The
class sizes can be any function chosen from the prescribed initial draw. -/
lemma card_initialPath_classOutput (m : ℕ) (hm : 0 < m) (t r N : ℕ)
    (indices attempts : List ℕ) (size start : ℕ → ℕ)
    (q : ℕ) (repValues : List ℕ)
    (hpath : ValidPath (fun _ => m) t (fun _ => 0) 0 r indices attempts)
    (hrep : ValidOutput size start 0 q repValues)
    (hbudget : bitBudget (fun _ => m) t 0 r +
      bitBudget size t 0 q ≤ N) :
    Nat.card {bits : List Bool // bits.length = N ∧
      TerminalFlatEvent (fun _ => m) t (fun _ => 0) 0 r
        indices attempts
        (fun rest => ∃ used charge,
          ClassTrace size t start 0 q rest repValues used charge false) bits} =
      stoppedWeight (fun _ => m) 0 attempts *
        jointWeight size t 0 q
          (N - consumedBits (fun _ => m) 0 attempts) := by
  classical
  have hfirst : bitBudget (fun _ => m) t 0 r ≤ N := by omega
  have hconsumed := ValidPath.consumedBits_le_budget
    (fun _ => m) t (fun _ => 0) hpath
  have htail : bitBudget size t 0 q ≤
      N - consumedBits (fun _ => m) 0 attempts := by omega
  rw [card_terminalFlatEvent (fun _ => m) t (fun _ => 0)
    hpath N hfirst]
  rw [card_flatPredicate]
  change stoppedWeight (fun _ => m) 0 attempts *
    (outputFiber size t start 0 q
      (N - consumedBits (fun _ => m) 0 attempts) repValues).card = _
  rw [card_outputFiber_valid size t start 0 q
    (N - consumedBits (fun _ => m) 0 attempts) repValues htail hrep]

/-- One prescribed initial index vector and one representative vector on
the same flat tape, with the first stopped vector left existential. -/
noncomputable def initialJointFiber (m t r N : ℕ) (indices : List ℕ)
    (size start : ℕ → ℕ) (q : ℕ) (repValues : List ℕ) :
    Finset (FlatTape N) := by
  classical
  exact Finset.univ.filter fun tape =>
    ∃ attempts,
      TerminalFlatEvent (fun _ => m) t (fun _ => 0) 0 r
        indices attempts
        (fun rest => ∃ used charge,
          ClassTrace size t start 0 q rest repValues used charge false)
        (flatBits tape)

private noncomputable def initialPathFiber (m t r N : ℕ)
    (indices attempts : List ℕ) (size start : ℕ → ℕ)
    (q : ℕ) (repValues : List ℕ) : Finset (FlatTape N) := by
  classical
  exact Finset.univ.filter fun tape =>
    TerminalFlatEvent (fun _ => m) t (fun _ => 0) 0 r
      indices attempts
      (fun rest => ∃ used charge,
        ClassTrace size t start 0 q rest repValues used charge false)
      (flatBits tape)

private lemma initialJointFiber_eq_biUnion (m t r N : ℕ)
    (indices : List ℕ) (size start : ℕ → ℕ) (q : ℕ)
    (repValues : List ℕ) :
    initialJointFiber m t r N indices size start q repValues =
      (attemptVectors t r).biUnion fun attempts =>
        initialPathFiber m t r N indices attempts size start q repValues := by
  classical
  ext tape
  simp only [initialJointFiber, initialPathFiber, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion]
  constructor
  · rintro ⟨attempts, hterminal⟩
    exact ⟨attempts, FlatClassSuccess.attempts_mem (fun _ => m) t
      (fun _ => 0) hterminal.1, hterminal⟩
  · rintro ⟨attempts, _, hterminal⟩
    exact ⟨attempts, hterminal⟩

private lemma outputCount_const (m d r : ℕ) :
    outputCount (fun _ => m) d r = m ^ r := by
  induction r generalizing d with
  | zero => simp [outputCount]
  | succ r ih => simp [outputCount, ih, pow_succ, mul_comm]

/-- The successful two-stage kernel is bounded by the ideal ordered-draw
law times the ideal uniform product of representatives, for each particular
draw and its own resulting class-size vector. The inequality is integer
cross-multiplication against the `2^N` equally likely flat tapes. -/
lemma initialJointFiber_le_ideal (m : ℕ) (hm : 0 < m)
    (t r N : ℕ) (indices : List ℕ) (size start : ℕ → ℕ)
    (q : ℕ) (repValues : List ℕ)
    (hindices : ValidOutput (fun _ => m) (fun _ => 0) 0 r indices)
    (hrep : ValidOutput size start 0 q repValues)
    (hbudget : bitBudget (fun _ => m) t 0 r +
      bitBudget size t 0 q ≤ N) :
    m ^ r * outputCount size 0 q *
      (initialJointFiber m t r N indices size start q repValues).card ≤
        2 ^ N := by
  classical
  let J := fun attempts =>
    initialPathFiber m t r N indices attempts size start q repValues
  have hfirstBudget : bitBudget (fun _ => m) t 0 r ≤ N := by omega
  have hcard (attempts : List ℕ) (ha : attempts ∈ attemptVectors t r) :
      (J attempts).card = stoppedWeight (fun _ => m) 0 attempts *
        jointWeight size t 0 q
          (N - consumedBits (fun _ => m) 0 attempts) := by
    let P : List Bool → Prop := fun rest => ∃ used charge,
      ClassTrace size t start 0 q rest repValues used charge false
    change (Finset.univ.filter fun tape : FlatTape N =>
      TerminalFlatEvent (fun _ => m) t (fun _ => 0) 0 r
        indices attempts P (flatBits tape)).card = _
    rw [← card_flatPredicate N _]
    exact card_initialPath_classOutput m hm t r N indices attempts
      size start q repValues
      (ValidOutput.validPath_of_mem (fun _ => m) t (fun _ => 0)
        hindices attempts ha) hrep hbudget
  have hbound (attempts : List ℕ) (ha : attempts ∈ attemptVectors t r) :
      outputCount size 0 q * (J attempts).card ≤
        stoppedWeight (fun _ => m) 0 attempts *
          2 ^ (N - consumedBits (fun _ => m) 0 attempts) := by
    have hpath := ValidOutput.validPath_of_mem (fun _ => m) t
      (fun _ => 0) hindices attempts ha
    have hcons := ValidPath.consumedBits_le_budget (fun _ => m)
      t (fun _ => 0) hpath
    have htail : bitBudget size t 0 q ≤
        N - consumedBits (fun _ => m) 0 attempts := by omega
    rw [hcard attempts ha]
    calc
      outputCount size 0 q *
          (stoppedWeight (fun _ => m) 0 attempts *
            jointWeight size t 0 q
              (N - consumedBits (fun _ => m) 0 attempts)) =
        stoppedWeight (fun _ => m) 0 attempts *
          (outputCount size 0 q *
            jointWeight size t 0 q
              (N - consumedBits (fun _ => m) 0 attempts)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (by
        simpa [card_outputFiber_valid size t start 0 q _ repValues htail hrep]
          using outputFiber_le_ideal_uniform size t start 0 q
            (N - consumedBits (fun _ => m) 0 attempts) repValues htail hrep)
  have hsum :
      outputCount size 0 q *
          (initialJointFiber m t r N indices size start q repValues).card ≤
        ∑ attempts ∈ attemptVectors t r,
          stoppedWeight (fun _ => m) 0 attempts *
            2 ^ (N - consumedBits (fun _ => m) 0 attempts) := by
    rw [initialJointFiber_eq_biUnion]
    calc
      outputCount size 0 q *
          ((attemptVectors t r).biUnion J).card ≤
        outputCount size 0 q *
          ∑ attempts ∈ attemptVectors t r, (J attempts).card :=
            Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ attempts ∈ attemptVectors t r,
          outputCount size 0 q * (J attempts).card := by
            rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum hbound
  have hfirst :
      (outputFiber (fun _ => m) t (fun _ => 0) 0 r N indices).card =
        ∑ attempts ∈ attemptVectors t r,
          stoppedWeight (fun _ => m) 0 attempts *
            2 ^ (N - consumedBits (fun _ => m) 0 attempts) := by
    rw [card_outputFiber_sum (fun _ => m) t (fun _ => 0) 0 r N
      indices hfirstBudget]
    apply Finset.sum_congr rfl
    intro attempts ha
    have hp := ValidOutput.validPath_of_mem (fun _ => m) t
      (fun _ => 0) hindices attempts ha
    simp [pathWeight, hp]
  have hfirstBound := outputFiber_le_ideal_uniform
    (fun _ => m) t (fun _ => 0) 0 r N indices hfirstBudget hindices
  rw [outputCount_const] at hfirstBound
  rw [hfirst] at hfirstBound
  calc
    m ^ r * outputCount size 0 q *
        (initialJointFiber m t r N indices size start q repValues).card =
      m ^ r * (outputCount size 0 q *
        (initialJointFiber m t r N indices size start q repValues).card) := by ring
    _ ≤ m ^ r * (∑ attempts ∈ attemptVectors t r,
          stoppedWeight (fun _ => m) 0 attempts *
            2 ^ (N - consumedBits (fun _ => m) 0 attempts)) :=
      Nat.mul_le_mul_left _ hsum
    _ ≤ 2 ^ N := hfirstBound

private lemma same_fixed_prefix {α : Type*} {xs ys as_ bs : List α}
    (hsize : xs.length = as_.length)
    (h : xs ++ ys = as_ ++ bs) : xs = as_ ∧ ys = bs := by
  have hp := congrArg (List.take xs.length) h
  have hs := congrArg (List.drop xs.length) h
  constructor
  · simpa [hsize] using hp
  · simpa [hsize] using hs

private lemma classTrace_accepted_inv (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) {d r : ℕ} {bits : List Bool}
    {values : List ℕ} {used charge : ℕ}
    (h : ClassTrace size t start d (r + 1) bits values used charge false) :
    ∃ (tape : BitTape (size d) t) (tail : List Bool)
      (i : Fin (size d)) (u : ℕ) (xs : List ℕ) (uz cz : ℕ),
      bits = tapeBits tape ++ tail ∧
      values = (start d + i.val) :: xs ∧
      used = u * Nat.clog 2 (size d) + uz ∧
      selectBitIndexWithCount (size d) (by have := i.isLt; omega)
        t tape = (some i, u) ∧
      ClassTrace size t start (d + 1) r
        ((tapeBits tape).drop (u * Nat.clog 2 (size d)) ++ tail)
        xs uz cz false := by
  cases h with
  | accepted tape tail i u hm hsel hnext =>
      exact ⟨tape, tail, i, u, _, _, _, rfl, rfl, rfl, hsel, hnext⟩

/-- Two successful traces on the same actual flat input read the same
number of bits, even if their proof witnesses and charges differ. -/
private lemma classTrace_used_unique (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {x y : List ℕ}
      {ux uy cx cy : ℕ},
      ClassTrace size t start d r bits x ux cx false →
      ClassTrace size t start d r bits y uy cy false → ux = uy
  | _, _, _, _, _, _, _, _, _, .done _ _, h₂ => by
      cases h₂
      rfl
  | d, _, _, _, _, _, _, _, _, .accepted tape₁ tail₁ i₁ u₁ hm₁ hs₁ hn₁,
      h₂ => by
      obtain ⟨tape₂, tail₂, i₂, u₂, ys, uy, cy,
        hbits, hvalues, hused, hs₂, hn₂⟩ :=
        classTrace_accepted_inv size t start h₂
      have hparts := same_fixed_prefix
        (by simp [tapeBits_length]) hbits
      have htape : tape₁ = tape₂ :=
        tapeBits_injective _ _ hparts.1
      subst tape₂
      have hsel : (some i₁, u₁) = (some i₂, u₂) := hs₁.symm.trans hs₂
      have hu : u₁ = u₂ := congrArg Prod.snd hsel
      subst u₂
      have htail : tail₁ = tail₂ := hparts.2
      subst tail₂
      have hrec := classTrace_used_unique size t start hn₁ hn₂
      omega

/-- Appending an unread suffix does not change any selector result or charge.
The source takes the suffix only after reading the actual stopping prefix. -/
private lemma classTrace_append (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {values : List ℕ}
      {used charge : ℕ} {failed : Bool},
      ClassTrace size t start d r bits values used charge failed →
      ∀ extra : List Bool,
        ClassTrace size t start d r (bits ++ extra) values used charge failed
  | _, _, _, _, _, _, _, .done d bits, extra => by
      exact ClassTrace.done d (bits ++ extra)
  | _, _, _, _, _, _, _, .failed tape tail u hm hsel, extra => by
      simpa only [List.append_assoc] using
        (ClassTrace.failed tape (tail ++ extra) u hm hsel)
  | _, _, _, _, _, _, _, .accepted (d := d) (r := r)
      (values := values) (used := used) (charge := charge)
      (failed := failed) tape tail i u hm hsel hnext, extra => by
      have hnext' := classTrace_append size t start hnext extra
      have hnext'' : ClassTrace size t start (d + 1) r
          ((tapeBits tape).drop (u * Nat.clog 2 (size d)) ++
            (tail ++ extra)) values used charge failed := by
        simpa only [List.append_assoc] using hnext'
      simpa only [List.append_assoc] using
        (ClassTrace.accepted (size := size) (t := t) (start := start)
          (d := d) (r := r) tape (tail ++ extra) i u hm hsel hnext'')

/-- The successful source trace's bit count is exactly the sum of its
stopped-prefix lengths. -/
lemma classTrace_success_flat_used (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) {d r : ℕ} {bits : List Bool}
    {values : List ℕ} {used charge : ℕ}
    (htrace : ClassTrace size t start d r bits values used charge false)
    (hbudget : bitBudget size t d r ≤ bits.length) :
    ∃ attempts,
      FlatClassSuccess size t start d r bits values attempts ∧
      consumedBits size d attempts = used := by
  obtain ⟨attempts, hflat⟩ :=
    classTrace_success_to_flat size t start htrace rfl
  obtain ⟨used', charge', hreconstructed, hused', _⟩ :=
    flatClassSuccess_to_classTrace size t start hflat hbudget
  have hunique := classTrace_used_unique size t start htrace hreconstructed
  exact ⟨attempts, hflat, hused'.symm.trans hunique.symm⟩

/-- A successful actual initial `DrawTrace`, followed by the actual
representative `ClassTrace`, lies in the counted two-stage flat event.
The representative trace starts at the exact unread bit after the draws. -/
lemma drawTrace_classTrace_mem_initialJointFiber
    (m : ℕ) (hm : 0 < m) (t r N : ℕ)
    (blocks : List (Fin (Nat.clog 2 m) → Bool))
    (extra : List Bool) (values : List (Fin m)) (used : ℕ)
    (hdraw : DrawTrace m hm t r blocks values used false)
    (size start : ℕ → ℕ) (q : ℕ) (repValues : List ℕ)
    (hclass : ∃ repUsed repCharge,
      ClassTrace size t start 0 q
        ((blocks.flatMap List.ofFn ++ extra).drop (used * Nat.clog 2 m))
        repValues repUsed repCharge false)
    (hbudget : bitBudget (fun _ => m) t 0 r ≤
      (blocks.flatMap List.ofFn ++ extra).length)
    (hlen : (blocks.flatMap List.ofFn ++ extra).length = N) :
    (flatBitsEquiv N).symm
      ⟨blocks.flatMap List.ofFn ++ extra, hlen⟩ ∈
      initialJointFiber m t r N (values.map Fin.val)
        size start q repValues := by
  classical
  obtain ⟨charge, hdrawClass⟩ := drawTrace_to_classTrace m hm t 0 hdraw
  have hdrawClass' := classTrace_append (fun _ => m) t
    (fun _ => 0) hdrawClass extra
  obtain ⟨attempts, hflat, hconsumed⟩ :=
    classTrace_success_flat_used (fun _ => m) t (fun _ => 0)
      hdrawClass' hbudget
  simp only [initialJointFiber, Finset.mem_filter, Finset.mem_univ,
    true_and]
  change ∃ attempts,
    TerminalFlatEvent (fun _ => m) t (fun _ => 0) 0 r
      (values.map Fin.val) attempts
      (fun rest => ∃ used charge,
        ClassTrace size t start 0 q rest repValues used charge false)
      (flatBits ((flatBitsEquiv N).symm
        ⟨blocks.flatMap List.ofFn ++ extra, hlen⟩))
  have hbits : flatBits ((flatBitsEquiv N).symm
      ⟨blocks.flatMap List.ofFn ++ extra, hlen⟩) =
      blocks.flatMap List.ofFn ++ extra :=
    congrArg Subtype.val
      ((flatBitsEquiv N).apply_symm_apply
        ⟨blocks.flatMap List.ofFn ++ extra, hlen⟩)
  rw [hbits]
  exact ⟨attempts, hflat, by simpa [hconsumed] using hclass⟩

private lemma outputCount_eq_finProd (size : ℕ → ℕ) (d r : ℕ) :
    outputCount size d r = ∏ j : Fin r, size (d + j.val) := by
  induction r generalizing d with
  | zero => simp [outputCount]
  | succ r ih =>
      rw [Fin.prod_univ_succ]
      simp only [outputCount, Fin.val_zero, Nat.add_zero]
      rw [ih (d + 1)]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      congr 1
      simp [Fin.val_succ]
      omega

/-- The numeric class-size product is precisely the number of ideal
representative choices in the existing hierarchical `InitialOutcome` law. -/
lemma repChoices_card_eq_outputCount
    {A C : Finset ℕ} {N : ℕ → Finset ℕ} {r q : ℕ}
    (draw : Fin r → A) (label size : ℕ → ℕ)
    (hrange : ∀ b ∈ C, label b < q)
    (hoccupied : LabelsOccupyPrefix q label C)
    (hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace N (drawSet A draw) b = trace N (drawSet A draw) b'))
    (hsizes : ∀ d < q, size d = classMultiplicity label C d) :
    Fintype.card (RepChoices A C N draw) = outputCount size 0 q := by
  classical
  have hchoices := Fintype.card_congr
    (numericChoicesEquiv draw label q hrange hoccupied hlabel)
  rw [Fintype.card_pi] at hchoices
  have hfactor (d : Fin q) :
      Fintype.card (NumericClassFiber C label q d) = size d.val := by
    simpa [NumericClassFiber, classMultiplicity, hsizes d.val d.isLt] using
      (Fintype.card_coe (C.filter fun b => label b = d.val))
  simp only [hfactor] at hchoices
  rw [outputCount_eq_finProd size 0 q]
  simpa using hchoices.symm

/-- A fixed successful flat-tape output has at most the existing
hierarchical model's weight for its ordered draw and representative choice.
This bound is per draw; the class-size product is allowed to vary with the
sample. `repValues` are the numeric positions written by the source. -/
lemma initialJointFiber_probability_le_outcomeWeight
    (A C : Finset ℕ) (Nhood : ℕ → Finset ℕ)
    (hA : A.Nonempty) (t r N q : ℕ)
    (draw : Fin r → A) (reps : RepChoices A C Nhood draw)
    (indices repValues : List ℕ) (label size : ℕ → ℕ)
    (hindices : ValidOutput (fun _ => A.card) (fun _ => 0) 0 r indices)
    (hrep : ValidOutput size (classStart size) 0 q repValues)
    (hrange : ∀ b ∈ C, label b < q)
    (hoccupied : LabelsOccupyPrefix q label C)
    (hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace Nhood (drawSet A draw) b =
          trace Nhood (drawSet A draw) b'))
    (hsizes : ∀ d < q, size d = classMultiplicity label C d)
    (hbudget : bitBudget (fun _ => A.card) t 0 r +
      bitBudget size t 0 q ≤ N) :
    ((initialJointFiber A.card t r N indices size (classStart size)
      q repValues).card : ℚ) / (2 ^ N : ℚ) ≤
      outcomeWeight A C Nhood r ⟨draw, reps⟩ := by
  classical
  have hm : 0 < A.card := Finset.card_pos.mpr hA
  have hcard := repChoices_card_eq_outputCount draw label size
    hrange hoccupied hlabel hsizes
  have hnat := initialJointFiber_le_ideal A.card hm t r N indices
    size (classStart size) q repValues hindices hrep hbudget
  rw [← hcard] at hnat
  have hnat' :
      (initialJointFiber A.card t r N indices size (classStart size)
        q repValues).card *
          (A.card ^ r * Fintype.card (RepChoices A C Nhood draw)) ≤
        2 ^ N := by
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnat
  have hrepNonempty : Nonempty (RepChoices A C Nhood draw) :=
    ⟨fun T => Classical.choice (repFiberNonempty A C Nhood draw T)⟩
  have hrepPos : 0 < Fintype.card (RepChoices A C Nhood draw) :=
    Fintype.card_pos_iff.mpr hrepNonempty
  have hden : 0 < (A.card ^ r : ℚ) *
      (Fintype.card (RepChoices A C Nhood draw) : ℚ) := by
    positivity
  have hpow : 0 < (2 ^ N : ℚ) := by positivity
  unfold outcomeWeight
  apply (div_le_div_iff₀ hpow hden).mpr
  have hnatQ :
      ((initialJointFiber A.card t r N indices size (classStart size)
        q repValues).card : ℚ) *
          ((A.card ^ r : ℚ) *
            (Fintype.card (RepChoices A C Nhood draw) : ℚ)) ≤
        (2 ^ N : ℚ) := by exact_mod_cast hnat'
  simpa [mul_assoc] using hnatQ

/-- Decode the exact source draw indices through its occupied domain-array
enumeration, retaining their order and repetitions. -/
noncomputable def sourceOrderedDraw (A : Finset ℕ) (m r : ℕ)
    (domain : ℕ → ℕ) (henum : PrefixEnumerates m domain A)
    (values : List (Fin m)) (hlen : values.length = r) : Fin r → A :=
  fun j => prefixDomainEnumeration m domain A henum
    ⟨values[j.val]'(by simpa [hlen] using j.isLt) |>.val,
      by
        have hcard := prefixEnumerates_card m domain A henum
        have hi := (values[j.val]'(by simpa [hlen] using j.isLt)).isLt
        omega⟩

lemma sourceOrderedDraw_val (A : Finset ℕ) (m r : ℕ)
    (domain : ℕ → ℕ) (henum : PrefixEnumerates m domain A)
    (values : List (Fin m)) (hlen : values.length = r) (j : Fin r) :
    (sourceOrderedDraw A m r domain henum values hlen j).val =
      domain (values[j.val]'(by simpa [hlen] using j.isLt)).val := by
  unfold sourceOrderedDraw
  exact prefixDomainEnumeration_lookup m domain A henum
    (values[j.val]'(by simpa [hlen] using j.isLt))

lemma sourceOrderedDraw_set (A : Finset ℕ) (m r : ℕ)
    (domain : ℕ → ℕ) (henum : PrefixEnumerates m domain A)
    (values : List (Fin m)) (hlen : values.length = r) :
    drawSet A (sourceOrderedDraw A m r domain henum values hlen) =
      (values.map fun i => domain i.val).toFinset := by
  let draw := sourceOrderedDraw A m r domain henum values hlen
  have hlist : (List.ofFn fun j : Fin r => (draw j : ℕ)) =
      values.map fun i => domain i.val := by
    apply List.ext_getElem
    · simp [hlen]
    · intro j hj hj'
      have hjr : j < r := by simpa [hlen] using hj'
      simpa [draw, List.getElem_ofFn, List.getElem_map] using
        sourceOrderedDraw_val A m r domain henum values hlen ⟨j, hjr⟩
  calc
    drawSet A draw = (List.ofFn fun j : Fin r => (draw j : ℕ)).toFinset := by
      ext x
      simp [drawSet, List.mem_ofFn]
    _ = _ := congrArg List.toFinset hlist

/-- Read the actual source's representative map once for every compact
numeric class. The common class formula ensures this is the same map that
the source wrote at every active vertex. -/
noncomputable def mappedNumericChoices (C : Finset ℕ)
    (label : ℕ → ℕ) (q : ℕ)
    (hoccupied : LabelsOccupyPrefix q label C)
    (mapped : ℕ → ℕ)
    (hrepC : ∀ b ∈ C, mapped b ∈ C)
    (hrepLabel : ∀ b ∈ C, label (mapped b) = label b) :
    ∀ d : Fin q, NumericClassFiber C label q d := by
  intro d
  let witness := labelWitness label q d hoccupied
  have hwC : witness.1 ∈ C := (Finset.mem_filter.mp witness.2).1
  refine ⟨mapped witness.1, Finset.mem_filter.mpr ⟨hrepC witness.1 hwC, ?_⟩⟩
  rw [hrepLabel witness.1 hwC]
  exact (Finset.mem_filter.mp witness.2).2

/-- The transported ideal outcome chooses exactly the representative stored
by the source on every active vertex. -/
lemma mappedNumericChoices_outcomeRep
    {A C : Finset ℕ} {Nhood : ℕ → Finset ℕ} {r q : ℕ}
    (draw : Fin r → A) (label : ℕ → ℕ)
    (hrange : ∀ b ∈ C, label b < q)
    (hoccupied : LabelsOccupyPrefix q label C)
    (hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace Nhood (drawSet A draw) b =
          trace Nhood (drawSet A draw) b'))
    (mapped code : ℕ → ℕ)
    (hrepC : ∀ b ∈ C, mapped b ∈ C)
    (hrepLabel : ∀ b ∈ C, label (mapped b) = label b)
    (hformula : ∀ b ∈ C, mapped b = code (label b))
    (b : ℕ) (hb : b ∈ C) :
    (outcomeChoice A C Nhood r
      ⟨draw, numericChoicesEquiv draw label q hrange hoccupied hlabel
        (mappedNumericChoices C label q hoccupied mapped hrepC hrepLabel)⟩).representative b =
      mapped b := by
  classical
  let d : Fin q := ⟨label b, hrange b hb⟩
  let witness := labelWitness label q d hoccupied
  have hwC : witness.1 ∈ C := (Finset.mem_filter.mp witness.2).1
  have hwLabel : label witness.1 = label b :=
    (Finset.mem_filter.mp witness.2).2
  have hindex :
      (⟨trace Nhood (drawSet A draw) b,
        Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩ : ClassIndex A C Nhood draw) =
      classIndexOfLabel draw label q hoccupied d := by
    apply Subtype.ext
    change trace Nhood (drawSet A draw) b =
      trace Nhood (drawSet A draw) witness.1
    exact (hlabel b hb witness.1 hwC).mp hwLabel.symm
  have hlookup := numericChoicesEquiv_lookup draw label q
    hrange hoccupied hlabel
    (mappedNumericChoices C label q hoccupied mapped hrepC hrepLabel) d
  dsimp only [outcomeChoice, decodeChoice]
  rw [dif_pos hb]
  change (numericChoicesEquiv draw label q hrange hoccupied hlabel
    (mappedNumericChoices C label q hoccupied mapped hrepC hrepLabel)
      ⟨trace Nhood (drawSet A draw) b,
        Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩).1 = mapped b
  rw [hindex, hlookup]
  change mapped witness.1 = mapped b
  rw [hformula witness.1 hwC, hformula b hb, hwLabel]

/-- Occupied compact labels fit in the active set even when the source's
partition implementation does not expose its internal class-count bound. -/
lemma occupied_classCount_le_card (C : Finset ℕ) (label : ℕ → ℕ) (q : ℕ)
    (hrange : ∀ b ∈ C, label b < q)
    (hoccupied : LabelsOccupyPrefix q label C) : q ≤ C.card := by
  classical
  have himage : C.image label = Finset.range q := by
    ext d
    constructor
    · intro hd
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hd
      exact Finset.mem_range.mpr (hrange b hb)
    · intro hd
      obtain ⟨b, hb⟩ := Finset.card_pos.mp
        (hoccupied d (Finset.mem_range.mp hd))
      exact Finset.mem_image.mpr
        ⟨b, (Finset.mem_filter.mp hb).1, (Finset.mem_filter.mp hb).2⟩
  calc
    q = (Finset.range q).card := (Finset.card_range q).symm
    _ = (C.image label).card := by rw [himage]
    _ ≤ C.card := Finset.card_image_le

private lemma constant_bitBudget (m t r : ℕ) :
    bitBudget (fun _ => m) t 0 r = r * t * Nat.clog 2 m := by
  have hconst : ∀ d r, bitBudget (fun _ => m) t d r =
      r * t * Nat.clog 2 m := by
    intro d r
    induction r generalizing d with
    | zero => simp [bitBudget]
    | succ r ih =>
        simp only [bitBudget, ih]
        ring
  exact hconst 0 r

private lemma class_bitBudget_le_uniform (size : ℕ → ℕ) (t q n : ℕ)
    (hsize : ∀ d < q, size d ≤ n) :
    bitBudget size t 0 q ≤ q * t * Nat.clog 2 n := by
  have hgeneral : ∀ d k, d + k ≤ q →
      bitBudget size t d k ≤ k * t * Nat.clog 2 n := by
    intro d k
    induction k generalizing d with
    | zero => simp [bitBudget]
    | succ k ih =>
        intro hdk
        have hd : d < q := by omega
        have hclog : Nat.clog 2 (size d) ≤ Nat.clog 2 n :=
          Nat.clog_mono_right 2 (hsize d hd)
        have hrec := ih (d + 1) (by omega)
        simp only [bitBudget]
        nlinarith
  exact hgeneral 0 q (by omega)

/-- The source's fixed reservation covers the sample-dependent two-stage
worst-case bit budget for every compact partition it can produce. -/
lemma initialSource_jointBudget
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (q : ℕ) (label size : ℕ → ℕ)
    (hsizes : ClassSizes n q I.activeB label size)
    (hoccupied : LabelsOccupyPrefix q label
      (activeVertices n I.activeB)) :
    bitBudget (fun _ => m) t 0 r + bitBudget size t 0 q ≤
      I.bits.length := by
  let C := activeVertices n I.activeB
  have hrange : ∀ b ∈ C, label b < q := by
    intro b hb
    exact hsizes.1 b (mem_activeVertices.mp hb).1
      (mem_activeVertices.mp hb).2
  have hq : q ≤ n :=
    (occupied_classCount_le_card C label q hrange hoccupied).trans
      (activeVertices_card_le n I.activeB)
  have hsize : ∀ d < q, size d ≤ n := by
    intro d hd
    rw [hsizes.2 d hd]
    exact (classMultiplicity_le_card _ _ _).trans
      (activeVertices_card_le n I.activeB)
  have hclass := class_bitBudget_le_uniform size t q n hsize
  rw [constant_bitBudget]
  calc
    r * t * Nat.clog 2 m + bitBudget size t 0 q ≤
        r * t * Nat.clog 2 m + q * t * Nat.clog 2 n :=
      Nat.add_le_add_left hclass _
    _ ≤ r * t * Nat.clog 2 m + n * t * Nat.clog 2 n := by
      gcongr
    _ ≤ I.bits.length := I.hbudget

/-- Coupling at the actual initial sampler's trace boundary: the same bit
list feeds the stopped indexed draws and then the sample-dependent class
selector. Every unread bit remains in the terminal suffix. -/
lemma initialSource_success_jointFiber
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (tape : Fin (r * t) → Fin (Nat.clog 2 m) → Bool)
    (tail : List Bool) (values : List (Fin m)) (used : ℕ)
    (hbits : I.bits = tapeBits tape ++ tail)
    (hdraw : DrawTrace m I.hmPos t r (List.ofFn tape) values used false)
    (W : Finset ℕ) (hW : W =
      (values.map fun i => I.domain i.val).toFinset)
    (hWA : W ⊆ A) (hlen : values.length = r)
    (q : ℕ) (label size sorted : ℕ → ℕ) (repValues : List ℕ)
    (repUsed repCharge : ℕ)
    (hclass : ClassTrace size t (classStart size) 0 q
      (I.bits.drop (used * Nat.clog 2 m))
      repValues repUsed repCharge false)
    (hsizes : ClassSizes n q I.activeB label size)
    (hoccupied : LabelsOccupyPrefix q label
      (activeVertices n I.activeB))
    (hclasses : ∀ b ∈ activeVertices n I.activeB,
      ∀ b' ∈ activeVertices n I.activeB,
        (label b = label b' ↔
          trace (numericNeighborhood G) W b =
            trace (numericNeighborhood G) W b'))
    (mapped : ℕ → ℕ)
    (hrepC : ∀ b ∈ activeVertices n I.activeB,
      mapped b ∈ activeVertices n I.activeB)
    (hrepLabel : ∀ b ∈ activeVertices n I.activeB,
      label (mapped b) = label b)
    (hformula : ∀ b ∈ activeVertices n I.activeB,
      mapped b = writeClassReps sorted I.repClass 0 repValues (label b)) :
    ∃ (draw : Fin r → A)
      (reps : RepChoices A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) draw),
      drawSet A draw = W ∧
      (flatBitsEquiv I.bits.length).symm ⟨I.bits, rfl⟩ ∈
        initialJointFiber m t r I.bits.length
          (values.map Fin.val) size (classStart size) q repValues ∧
      ((initialJointFiber m t r I.bits.length
        (values.map Fin.val) size (classStart size) q repValues).card : ℚ) /
          (2 ^ I.bits.length : ℚ) ≤
        outcomeWeight A (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) r ⟨draw, reps⟩ ∧
      ∀ b ∈ activeVertices n I.activeB,
        (outcomeChoice A (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) r
          ⟨draw, reps⟩).representative b = mapped b := by
  classical
  let C := activeVertices n I.activeB
  let Nhood := fun b => numericNeighborhood G b ∩ A
  let draw := sourceOrderedDraw A m r I.domain I.henum values hlen
  have hm : A.card = m := (prefixEnumerates_card m I.domain A I.henum).symm
  have hdrawSet : drawSet A draw = W := by
    simpa [draw, hW] using
      sourceOrderedDraw_set A m r I.domain I.henum values hlen
  have hrange : ∀ b ∈ C, label b < q := by
    intro b hb
    exact hsizes.1 b (mem_activeVertices.mp hb).1
      (mem_activeVertices.mp hb).2
  have hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace Nhood (drawSet A draw) b =
          trace Nhood (drawSet A draw) b') := by
    intro b hb b' hb'
    rw [hdrawSet, restrictedNeighborhood_trace_eq _ hWA,
      restrictedNeighborhood_trace_eq _ hWA]
    exact hclasses b hb b' hb'
  let reps := numericChoicesEquiv draw label q hrange hoccupied hlabel
    (mappedNumericChoices C label q hoccupied mapped hrepC hrepLabel)
  refine ⟨draw, reps, hdrawSet, ?_, ?_, ?_⟩
  · have hfirst : bitBudget (fun _ => m) t 0 r ≤ I.bits.length :=
      le_trans (Nat.le_add_right _ _)
        (initialSource_jointBudget I q label size hsizes hoccupied)
    have hlist : (List.ofFn tape).flatMap List.ofFn ++ tail = I.bits := by
      simpa [tapeBits] using hbits.symm
    have hmem := drawTrace_classTrace_mem_initialJointFiber m I.hmPos
      t r I.bits.length (List.ofFn tape) tail values used hdraw
      size (classStart size) q repValues
      (by
        refine ⟨repUsed, repCharge, ?_⟩
        simpa [hlist] using hclass)
      (by simpa [hlist] using hfirst)
      (by simp [hlist])
    simpa [hlist] using hmem
  · obtain ⟨charge, hdrawClass⟩ := drawTrace_to_classTrace m I.hmPos t 0 hdraw
    obtain ⟨attempts, hflatDraw⟩ :=
      classTrace_success_to_flat (fun _ => m) t (fun _ => 0)
        hdrawClass rfl
    have hindices : ValidOutput (fun _ => m) (fun _ => 0) 0 r
        (values.map Fin.val) :=
      ValidPath.validOutput (fun _ => m) t (fun _ => 0)
        (FlatClassSuccess.validPath (fun _ => m) t (fun _ => 0) hflatDraw)
    obtain ⟨attemptsRep, hflatRep⟩ :=
      classTrace_success_to_flat size t (classStart size) hclass rfl
    have hrep : ValidOutput size (classStart size) 0 q repValues :=
      ValidPath.validOutput size t (classStart size)
        (FlatClassSuccess.validPath size t (classStart size) hflatRep)
    have hbudget := initialSource_jointBudget I q label size hsizes hoccupied
    have hprob := initialJointFiber_probability_le_outcomeWeight
      A C Nhood I.hAnonempty t r I.bits.length q draw reps
      (values.map Fin.val) repValues label size
      (by simpa [hm] using hindices) hrep hrange hoccupied
      hlabel hsizes.2 (by simpa [hm] using hbudget)
    simpa [hm, C, Nhood, reps] using hprob
  · intro b hb
    exact mappedNumericChoices_outcomeRep draw label hrange hoccupied
      hlabel mapped (fun d => writeClassReps sorted I.repClass 0 repValues d)
      hrepC hrepLabel hformula b hb

set_option maxHeartbeats 800000 in
/-- The executed initial sampler exposes its actual successful flat-tape
event and a pointwise subprobability bound for the exact source output. -/
lemma initialSamplerAttempt_run_jointFiber
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A) :
    ∃ (σ' : Env) (tape : Fin (r * t) → Fin (Nat.clog 2 m) → Bool)
      (tail : List Bool) (values : List (Fin m)) (used : ℕ)
      (drawFailed : Bool) (stageCost : ℕ),
      I.bits = tapeBits tape ++ tail ∧
      DrawTrace m I.hmPos t r (List.ofFn tape) values used drawFailed ∧
      Run B initialSamplerAttempt I.σ σ'
        (2 + initialDrawSampleCost n m used
          (values.length + if drawFailed then 1 else 0)
          values.length drawFailed +
          (if drawFailed then 5 else 4 + stageCost)) ∧
      (drawFailed = false → σ'.vars "repFailed" = 0 →
        ∃ (W : Finset ℕ) (q : ℕ) (size : ℕ → ℕ)
          (repValues : List ℕ) (mapped : ℕ → ℕ)
          (draw : Fin r → A)
          (reps : RepChoices A (activeVertices n I.activeB)
            (fun b => numericNeighborhood G b ∩ A) draw),
          σ'.arrs "repB" = arrOf n mapped ∧
          drawSet A draw = W ∧
          (flatBitsEquiv I.bits.length).symm ⟨I.bits, rfl⟩ ∈
            initialJointFiber m t r I.bits.length
              (values.map Fin.val) size (classStart size) q repValues ∧
          ((initialJointFiber m t r I.bits.length
            (values.map Fin.val) size (classStart size) q repValues).card : ℚ) /
              (2 ^ I.bits.length : ℚ) ≤
            outcomeWeight A (activeVertices n I.activeB)
              (fun b => numericNeighborhood G b ∩ A) r ⟨draw, reps⟩ ∧
          ∀ b ∈ activeVertices n I.activeB,
            (outcomeChoice A (activeVertices n I.activeB)
              (fun b => numericNeighborhood G b ∩ A) r
              ⟨draw, reps⟩).representative b = mapped b) := by
  obtain ⟨_σd, σ', tape, tail, values, used, drawFailed, stageCost,
    hbits, hdrawTrace, hrun, _haccepted, _hn, _hqpow, _hbatchFailed,
    _harrFrame, _hvarFrame, _hdrawFailure, hdrawSuccess,
    _hdrawRun, _hdrawInp⟩ :=
      Lax457868Proofs.InitialSamplerAttempt.initialSamplerAttempt_run_bits I
  refine ⟨σ', tape, tail, values, used, drawFailed, stageCost,
    hbits, hdrawTrace, hrun, ?_⟩
  intro hdrawOK hrepOK
  obtain ⟨W, _sampleOrd, _sampleCount, _σp, q, label, size, _xs, sorted,
    repValues, repUsed, repCharge, repFailed, hW, hWA, _hWcard,
    hlen, _hprefix, _hpartition, hsizes, hoccupied, hclasses,
    _hselection, _hnFinal, _hqpowFinal, _hsampleCount, _hclassB,
    _hclassSize, _hord, _hnodup, hxs, hclass, _hrepUsedLe,
    hrepFailedVal, _hrepFailure, _hsampleFlags, _hinp,
    hrepSuccess, _hcost, _hsourceCert⟩ := hdrawSuccess hdrawOK
  have hrepFalse : repFailed = false := by
    cases repFailed with
    | false => rfl
    | true => simp [hrepFailedVal] at hrepOK
  obtain ⟨mapped, hmappedArr, _hvFinal, hformulaSource, hrepClass⟩ :=
    hrepSuccess hrepFalse
  let C := activeVertices n I.activeB
  have hrepC : ∀ b ∈ C, mapped b ∈ C := by
    intro b hb
    obtain ⟨hbn, hbactive⟩ := mem_activeVertices.mp hb
    change mapped b ∈ activeVertices n I.activeB
    rw [← hxs]
    exact List.mem_toFinset.mpr (hrepClass b hbn hbactive).2.1
  have hrepLabel : ∀ b ∈ C, label (mapped b) = label b := by
    intro b hb
    obtain ⟨hbn, hbactive⟩ := mem_activeVertices.mp hb
    exact (hrepClass b hbn hbactive).2.2
  have hformula : ∀ b ∈ C,
      mapped b = writeClassReps sorted I.repClass 0 repValues (label b) := by
    intro b hb
    obtain ⟨hbn, hbactive⟩ := mem_activeVertices.mp hb
    exact hformulaSource b hbn hbactive
  obtain ⟨draw, reps, hdrawSet, hmem, hprob, hrepresentative⟩ :=
    initialSource_success_jointFiber I tape tail values used hbits
      (by simpa [hdrawOK] using hdrawTrace) W hW hWA hlen
      q label size sorted repValues repUsed repCharge
      (by simpa [hrepFalse] using hclass) hsizes hoccupied
      hclasses mapped hrepC hrepLabel hformula
  exact ⟨W, q, size, repValues, mapped, draw, reps,
    hmappedArr, hdrawSet, hmem, hprob, hrepresentative⟩

/-- Compact class sizes fill exactly the active prefix of the sorted array. -/
lemma classStart_eq_card_of_sizes (C : Finset ℕ) (label size : ℕ → ℕ)
    (q : ℕ) (hrange : ∀ b ∈ C, label b < q)
    (hsizes : ∀ d < q, size d = classMultiplicity label C d) :
    classStart size q = C.card := by
  have hsum : ∀ k, classStart size k =
      ∑ d ∈ Finset.range k, size d := by
    intro k
    induction k with
    | zero => simp [classStart]
    | succ k ih => simp [classStart, ih, Finset.sum_range_succ]
  rw [hsum]
  have heq : (∑ d ∈ Finset.range q, size d) =
      ∑ d ∈ Finset.range q, classMultiplicity label C d := by
    apply Finset.sum_congr rfl
    intro d hd
    exact hsizes d (Finset.mem_range.mp hd)
  rw [heq]
  exact sum_classMultiplicity_of_bounded hrange

private lemma validOutput_length_and_bound (size : ℕ → ℕ) :
    ∀ {d q : ℕ} {values : List ℕ},
      ValidOutput size (classStart size) d q values →
      values.length = q ∧
      ∀ v ∈ values, v < classStart size (d + q)
  | _, _, _, .done _ => by simp
  | _, _, _, .step (d := d) (r := r) i hnext => by
      obtain ⟨hlen, hbound⟩ := validOutput_length_and_bound size hnext
      constructor
      · simp [hlen]
      · intro v hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv
        · have hhead : classStart size d + i.val <
              classStart size (d + 1) := by
            simp only [classStart]
            omega
          exact hhead.trans_le (classStart_mono size (by omega))
        · have htail := hbound v hv
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail

/-- Sum conditional class-selector bounds over disjoint *concrete* stopped
draw prefixes. The class-size vector may change with the entire first-stage
prefix; only its ideal output count has to agree. -/
lemma adaptiveInitialFiber_le_ideal
    (m : ℕ) (hm : 0 < m) (t r N k : ℕ)
    (indices : List ℕ)
    (size start : List ℕ → ℕ → ℕ)
    (q : List ℕ → ℕ) (repValues : List ℕ → List ℕ)
    (hindices : ValidOutput (fun _ => m) (fun _ => 0) 0 r indices)
    (hfirstBudget : bitBudget (fun _ => m) t 0 r ≤ N)
    (hrep : ∀ a ∈ attemptVectors t r,
      ValidOutput (size a) (start a) 0 (q a) (repValues a))
    (hbudget : ∀ a ∈ attemptVectors t r,
      bitBudget (fun _ => m) t 0 r +
        bitBudget (size a) t 0 (q a) ≤ N)
    (hcount : ∀ a ∈ attemptVectors t r,
      outputCount (size a) 0 (q a) = k) :
    m ^ r * k *
      ((attemptVectors t r).biUnion fun a =>
        initialPathFiber m t r N indices a
          (size a) (start a) (q a) (repValues a)).card ≤ 2 ^ N := by
  classical
  let J := fun a => initialPathFiber m t r N indices a
    (size a) (start a) (q a) (repValues a)
  let K := fun a => pathFiber (fun _ => m) t (fun _ => 0) 0 r N indices a
  have hsub (a : List ℕ) : J a ⊆ K a := by
    intro tape ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp ht).2.1⟩
  have hJdisj : ∀ a ∈ attemptVectors t r, ∀ b ∈ attemptVectors t r,
      a ≠ b → Disjoint (J a) (J b) := by
    intro a _ b _ hab
    exact (pathFiber_disjoint (fun _ => m) t (fun _ => 0)
      0 r N indices hab).mono (hsub a) (hsub b)
  have hcardJ (a : List ℕ) (ha : a ∈ attemptVectors t r) :
      (J a).card = stoppedWeight (fun _ => m) 0 a *
        jointWeight (size a) t 0 (q a)
          (N - consumedBits (fun _ => m) 0 a) := by
    have hpath := ValidOutput.validPath_of_mem (fun _ => m) t
      (fun _ => 0) hindices a ha
    have h := card_initialPath_classOutput m hm t r N indices a
      (size a) (start a) (q a) (repValues a)
      hpath (hrep a ha) (hbudget a ha)
    simpa [J, initialPathFiber, ← card_flatPredicate] using h
  have hcardK (a : List ℕ) (ha : a ∈ attemptVectors t r) :
      (K a).card = stoppedWeight (fun _ => m) 0 a *
        2 ^ (N - consumedBits (fun _ => m) 0 a) := by
    have hpath := ValidOutput.validPath_of_mem (fun _ => m) t
      (fun _ => 0) hindices a ha
    have h := card_flatClassSuccess (fun _ => m) t (fun _ => 0)
      hpath N hfirstBudget
    have hcard := card_flatPredicate N
      (fun bits => FlatClassSuccess (fun _ => m) t (fun _ => 0)
        0 r bits indices a)
    simpa [K, pathFiber] using hcard.symm.trans h
  have hper (a : List ℕ) (ha : a ∈ attemptVectors t r) :
      k * (J a).card ≤ (K a).card := by
    have hpath := ValidOutput.validPath_of_mem (fun _ => m) t
      (fun _ => 0) hindices a ha
    have hconsumed := ValidPath.consumedBits_le_budget
      (fun _ => m) t (fun _ => 0) hpath
    have htail : bitBudget (size a) t 0 (q a) ≤
        N - consumedBits (fun _ => m) 0 a := by
      have hb := hbudget a ha
      omega
    have hclass := outputFiber_le_ideal_uniform (size a) t
      (start a) 0 (q a)
      (N - consumedBits (fun _ => m) 0 a) (repValues a)
      htail (hrep a ha)
    rw [card_outputFiber_valid (size a) t (start a) 0 (q a)
      (N - consumedBits (fun _ => m) 0 a) (repValues a)
      htail (hrep a ha), hcount a ha] at hclass
    rw [hcardJ a ha, hcardK a ha]
    nlinarith [Nat.mul_le_mul_left (stoppedWeight (fun _ => m) 0 a) hclass]
  have hsum : k * ((attemptVectors t r).biUnion J).card ≤
      (outputFiber (fun _ => m) t (fun _ => 0) 0 r N indices).card := by
    rw [Finset.card_biUnion hJdisj,
      outputFiber_eq_biUnion (fun _ => m) t (fun _ => 0)
        0 r N indices hfirstBudget,
      Finset.card_biUnion]
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun a ha => hper a ha
    · intro a ha b hb hab
      exact pathFiber_disjoint (fun _ => m) t (fun _ => 0)
        0 r N indices hab
  have hfirst := outputFiber_le_ideal_uniform (fun _ => m) t
    (fun _ => 0) 0 r N indices hfirstBudget hindices
  rw [outputCount_const m 0 r] at hfirst
  calc
    m ^ r * k * ((attemptVectors t r).biUnion J).card =
        m ^ r * (k * ((attemptVectors t r).biUnion J).card) := by ring
    _ ≤ m ^ r *
        (outputFiber (fun _ => m) t (fun _ => 0) 0 r N indices).card :=
      Nat.mul_le_mul_left _ hsum
    _ ≤ 2 ^ N := hfirst

private lemma sorted_prefix_injective (xs : List ℕ) (sorted label : ℕ → ℕ)
    (Q q : ℕ) (hxs : xs.Nodup)
    (hlabel : ∀ b ∈ xs, label b < Q)
    (hsorted : ∀ i < xs.length,
      sorted i = (bucketSort Q label xs).getD i 0) :
    ∀ i < xs.length, ∀ j < xs.length,
      sorted i = sorted j → i = j := by
  intro i hi j hj hij
  have hlen : (bucketSort Q label xs).length = xs.length :=
    length_bucketSort hxs hlabel
  have hi' : i < (bucketSort Q label xs).length := by rwa [hlen]
  have hj' : j < (bucketSort Q label xs).length := by rwa [hlen]
  apply ((nodup_bucketSort hxs).getElem_inj_iff (hi := hi')
    (hj := hj')).mp
  have hget := (hsorted i hi).symm.trans (hij.trans (hsorted j hj))
  simpa [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hj'] using hget

/-- For a fixed source partition and sorted class array, the abstract
representative map determines the numeric class-position vector uniquely. -/
lemma numericRepValues_unique_of_mapped
    (C : Finset ℕ) (label size sorted repClass : ℕ → ℕ)
    (q : ℕ) (xs : List ℕ) (Q : ℕ)
    (hrange : ∀ b ∈ C, label b < q)
    (hoccupied : LabelsOccupyPrefix q label C)
    (hsizes : ∀ d < q, size d = classMultiplicity label C d)
    (hxs : xs.Nodup) (hxsSet : xs.toFinset = C)
    (hlen : xs.length = C.card)
    (hsorted : ∀ i < xs.length,
      sorted i = (bucketSort Q label xs).getD i 0)
    (hqQ : q ≤ Q)
    (a b : List ℕ)
    (ha : ValidOutput size (classStart size) 0 q a)
    (hb : ValidOutput size (classStart size) 0 q b)
    (mapped : ℕ → ℕ)
    (hmapA : ∀ v ∈ C,
      mapped v = writeClassReps sorted repClass 0 a (label v))
    (hmapB : ∀ v ∈ C,
      mapped v = writeClassReps sorted repClass 0 b (label v)) :
    a = b := by
  classical
  have hlabelXs : ∀ v ∈ xs, label v < Q := by
    intro v hv
    exact (hrange v (hxsSet ▸ List.mem_toFinset.mpr hv)).trans_le hqQ
  have hinj := sorted_prefix_injective xs sorted label Q q hxs hlabelXs hsorted
  obtain ⟨hlenA, hboundA⟩ := validOutput_length_and_bound size ha
  obtain ⟨hlenB, hboundB⟩ := validOutput_length_and_bound size hb
  have hcap : classStart size q = xs.length :=
    (classStart_eq_card_of_sizes C label size q hrange hsizes).trans hlen.symm
  apply List.ext_getElem
  · omega
  · intro d hda hdb
    have hd : d < q := by omega
    let w := labelWitness label q ⟨d, hd⟩ hoccupied
    have hwC : w.1 ∈ C := (Finset.mem_filter.mp w.2).1
    have hwLabel : label w.1 = d := (Finset.mem_filter.mp w.2).2
    have hposA : a[d] < xs.length := by
      rw [← hcap]
      simpa using hboundA a[d] (List.getElem_mem hda)
    have hposB : b[d] < xs.length := by
      rw [← hcap]
      simpa using hboundB b[d] (List.getElem_mem hdb)
    have hmaps : writeClassReps sorted repClass 0 a d =
        writeClassReps sorted repClass 0 b d := by
      have hA := hmapA w.1 hwC
      have hB := hmapB w.1 hwC
      rw [hwLabel] at hA hB
      exact hA.symm.trans hB
    have hlookupA := writeClassReps_at sorted repClass 0 a d hda
    have hlookupB := writeClassReps_at sorted repClass 0 b d hdb
    simp only [zero_add] at hlookupA hlookupB
    rw [hlookupA, hlookupB] at hmaps
    exact hinj a[d] hposA b[d] hposB hmaps

/-- Two bounded source runs with the same initial state and consumed input
prefix have identical scalar/array/output states; only their unread input
suffixes differ. -/
lemma run_same_consumedPrefix
    {B : ℕ} {c : Com} {σ τ τ' : Env} {K K' : ℕ}
    (pre rest rest' : List ℕ)
    (hinput : σ.inp = pre ++ rest)
    (houtput : τ.inp = rest)
    (h : Run B c σ τ K)
    (h' : Run B c {σ with inp := pre ++ rest'} τ' K') :
    τ' = {τ with inp := rest'} := by
  obtain ⟨k, _, hbig⟩ := h
  obtain ⟨k', _, hbig'⟩ := h'
  obtain ⟨read, hsplit, _, htransport⟩ :=
    Lax457868Proofs.SourceTapePrefix.consumed_prefix hbig
  have hread : read = pre := by
    rw [houtput] at hsplit
    rw [hinput] at hsplit
    exact List.append_cancel_right hsplit.symm
  subst read
  have htransport' := htransport rest'
  obtain ⟨hfinal, _⟩ := BigStep.unique htransport'.bigStep hbig'.bigStep
  exact hfinal.symm

/-- Fixing every bit consumed by the first stage leaves exactly the
fixed-length suffix event. In particular the rejected selector blocks are
part of the condition, rather than being averaged away. -/
lemma card_fixedConsumedPrefix (N u : ℕ) (hu : u ≤ N)
    (pre : List Bool) (hpre : pre.length = u)
    (P : List Bool → Prop) :
    Nat.card {bits : List Bool // bits.length = N ∧
      bits.take u = pre ∧ P (bits.drop u)} =
    Nat.card {rest : List Bool // rest.length = N - u ∧ P rest} := by
  let e : {bits : List Bool // bits.length = N ∧
      bits.take u = pre ∧ P (bits.drop u)} ≃
      {rest : List Bool // rest.length = N - u ∧ P rest} := {
    toFun := fun bits => ⟨bits.1.drop u, by
      simp [bits.2.1, hu], bits.2.2.2⟩
    invFun := fun rest => ⟨pre ++ rest.1, by
      simp [hpre, rest.2.1, hu], by
        simp [hpre], by
          simpa [hpre] using rest.2.2⟩
    left_inv := by
      intro bits
      apply Subtype.ext
      simpa only [bits.2.2.1] using (List.take_append_drop u bits.1)
    right_inv := by
      intro rest
      apply Subtype.ext
      simp [hpre]
  }
  exact Nat.card_congr e

/-- A suffix law may depend on every consumed bit of the first stage. Its
per-prefix domination sums without assuming those bits determine only an
abstract index or stopping-count vector. -/
lemma adaptiveConsumedPrefix_le (N u k : ℕ) (hu : u ≤ N)
    (P : List Bool → Prop) (Q : List Bool → List Bool → Prop)
    (hQ : ∀ pre : List Bool, pre.length = u → P pre →
      k * Nat.card {rest : List Bool // rest.length = N - u ∧ Q pre rest} ≤
        2 ^ (N - u)) :
    k * Nat.card {bits : List Bool // bits.length = N ∧
      P (bits.take u) ∧ Q (bits.take u) (bits.drop u)} ≤
      Nat.card {bits : List Bool // bits.length = N ∧ P (bits.take u)} := by
  classical
  let J : FlatTape u → Finset (FlatTape N) := fun pre =>
    Finset.univ.filter fun tape =>
      P (flatBits pre) ∧ (flatBits tape).take u = flatBits pre ∧
        Q (flatBits pre) ((flatBits tape).drop u)
  let K : FlatTape u → Finset (FlatTape N) := fun pre =>
    Finset.univ.filter fun tape =>
      P (flatBits pre) ∧ (flatBits tape).take u = flatBits pre
  have hpre (pre : FlatTape u) : (flatBits pre).length = u := flatBits_length pre
  have hJdisj : ∀ a ∈ (Finset.univ : Finset (FlatTape u)),
      ∀ b ∈ (Finset.univ : Finset (FlatTape u)),
      a ≠ b → Disjoint (J a) (J b) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro tape ha hb
    have hea := (Finset.mem_filter.mp ha).2.2.1
    have heb := (Finset.mem_filter.mp hb).2.2.1
    exact hab ((flatBitsEquiv u).injective (by
      apply Subtype.ext
      exact hea.symm.trans heb))
  have hKdisj : ∀ a ∈ (Finset.univ : Finset (FlatTape u)),
      ∀ b ∈ (Finset.univ : Finset (FlatTape u)),
      a ≠ b → Disjoint (K a) (K b) := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro tape ha hb
    have hea := (Finset.mem_filter.mp ha).2.2
    have heb := (Finset.mem_filter.mp hb).2.2
    exact hab ((flatBitsEquiv u).injective (by
      apply Subtype.ext
      exact hea.symm.trans heb))
  have hJunion : (Finset.univ : Finset (FlatTape u)).biUnion J =
      Finset.univ.filter (fun tape : FlatTape N =>
        P ((flatBits tape).take u) ∧
          Q ((flatBits tape).take u) ((flatBits tape).drop u)) := by
    ext tape
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, J]
    constructor
    · rintro ⟨pre, hp, heq, hq⟩
      exact ⟨heq ▸ hp, heq ▸ hq⟩
    · rintro ⟨hp, hq⟩
      let pre : FlatTape u :=
        (flatBitsEquiv u).symm ⟨(flatBits tape).take u, by
          simp [flatBits_length, hu]⟩
      have heq : flatBits pre = (flatBits tape).take u := by
        exact congrArg Subtype.val ((flatBitsEquiv u).apply_symm_apply _)
      exact ⟨pre, heq ▸ hp, heq.symm, heq ▸ hq⟩
  have hKunion : (Finset.univ : Finset (FlatTape u)).biUnion K =
      Finset.univ.filter (fun tape : FlatTape N =>
        P ((flatBits tape).take u)) := by
    ext tape
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, K]
    constructor
    · rintro ⟨pre, hp, heq⟩
      exact heq ▸ hp
    · intro hp
      let pre : FlatTape u :=
        (flatBitsEquiv u).symm ⟨(flatBits tape).take u, by
          simp [flatBits_length, hu]⟩
      have heq : flatBits pre = (flatBits tape).take u := by
        exact congrArg Subtype.val ((flatBitsEquiv u).apply_symm_apply _)
      exact ⟨pre, heq ▸ hp, heq.symm⟩
  have hcardAll : Nat.card {rest : List Bool // rest.length = N - u ∧ True} =
      2 ^ (N - u) := by
    let e : {rest : List Bool // rest.length = N - u ∧ True} ≃
        {rest : List Bool // rest.length = N - u} := {
      toFun := fun x => ⟨x.1, x.2.1⟩
      invFun := fun x => ⟨x.1, x.2, trivial⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
    }
    rw [Nat.card_congr e, ← Nat.card_congr (flatBitsEquiv (N - u)),
      Nat.card_eq_fintype_card]
    simp [FlatTape]
  have hper (pre : FlatTape u) : k * (J pre).card ≤ (K pre).card := by
    by_cases hp : P (flatBits pre)
    · have hj : (J pre).card = Nat.card {rest : List Bool //
          rest.length = N - u ∧ Q (flatBits pre) rest} := by
        change (Finset.univ.filter fun tape : FlatTape N =>
          P (flatBits pre) ∧ (flatBits tape).take u = flatBits pre ∧
            Q (flatBits pre) ((flatBits tape).drop u)).card = _
        simp only [hp, true_and]
        exact (card_flatPredicate N (fun bits =>
          bits.take u = flatBits pre ∧
            Q (flatBits pre) (bits.drop u))).symm.trans
          (card_fixedConsumedPrefix N u hu (flatBits pre)
            (hpre pre) (Q (flatBits pre)))
      have hk : (K pre).card = 2 ^ (N - u) := by
        change (Finset.univ.filter fun tape : FlatTape N =>
          P (flatBits pre) ∧ (flatBits tape).take u = flatBits pre).card = _
        simp only [hp, true_and]
        have h := (card_flatPredicate N (fun bits =>
          bits.take u = flatBits pre)).symm
        have hfixed := (card_fixedConsumedPrefix N u hu
          (flatBits pre) (hpre pre) (fun _ => True)).trans hcardAll
        exact h.trans (by simpa only [and_true] using hfixed)
      rw [hj, hk]
      exact hQ (flatBits pre) (hpre pre) hp
    · have hj : J pre = ∅ := by simp [J, hp]
      have hk : K pre = ∅ := by simp [K, hp]
      simp [hj, hk]
  have hnum : Nat.card {bits : List Bool // bits.length = N ∧
        P (bits.take u) ∧ Q (bits.take u) (bits.drop u)} =
      ((Finset.univ : Finset (FlatTape u)).biUnion J).card := by
    rw [hJunion]
    exact card_flatPredicate N _
  have hden : Nat.card {bits : List Bool // bits.length = N ∧
        P (bits.take u)} =
      ((Finset.univ : Finset (FlatTape u)).biUnion K).card := by
    rw [hKunion]
    exact card_flatPredicate N _
  rw [hnum, hden, Finset.card_biUnion hJdisj,
    Finset.card_biUnion hKdisj, Finset.mul_sum]
  exact Finset.sum_le_sum fun pre _ => hper pre

private lemma flatClassSuccess_append_suffix (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {values attempts : List ℕ},
      FlatClassSuccess size t start d r bits values attempts →
      ∀ rest, FlatClassSuccess size t start d r (bits ++ rest)
        values attempts
  | _, _, _, _, _, .done d bits, rest => by
      simpa using (FlatClassSuccess.done d (bits ++ rest))
  | _, _, _, _, _, .step i pre suffix hm hu hp hnext, rest => by
      simpa only [List.append_assoc] using
        (FlatClassSuccess.step i pre (suffix ++ rest) hm hu hp
          (flatClassSuccess_append_suffix size t start hnext rest))

private lemma flatClassSuccess_take_consumed (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {values attempts : List ℕ},
      FlatClassSuccess size t start d r bits values attempts →
      FlatClassSuccess size t start d r
        (bits.take (consumedBits size d attempts)) values attempts
  | _, _, _, _, _, .done d bits => by
      simpa [consumedBits] using (FlatClassSuccess.done d [])
  | _, _, _, _, _, .step (d := d) (v := v) (attempts := attempts)
      i pre suffix hm hu hp hnext => by
      have hnext' := flatClassSuccess_take_consumed size t start hnext
      have hstep := FlatClassSuccess.step i pre
        (suffix.take (consumedBits size (d + 1) attempts)) hm hu hp hnext'
      have htake : (tapeBits pre).take
          ((v + 1) * Nat.clog 2 (size d) +
            consumedBits size (d + 1) attempts) = tapeBits pre := by
        apply List.take_of_length_le
        simp [tapeBits_length]
      simpa [consumedBits, tapeBits_length, List.take_append, htake] using hstep

lemma flatClassSuccess_iff_consumedPrefix (size : ℕ → ℕ) (t : ℕ)
    (start : ℕ → ℕ) (d r : ℕ) (bits : List Bool)
    (values attempts : List ℕ) :
    FlatClassSuccess size t start d r bits values attempts ↔
      FlatClassSuccess size t start d r
        (bits.take (consumedBits size d attempts)) values attempts := by
  constructor
  · exact flatClassSuccess_take_consumed size t start
  · intro h
    have h' := flatClassSuccess_append_suffix size t start h
      (bits.drop (consumedBits size d attempts))
    simpa only [List.take_append_drop] using h'

/-- On one stopped first-stage path, class sizes and the desired numeric
representative vector may depend on the entire consumed bit prefix. -/
lemma adaptiveInitialPath_le_ideal
    (m : ℕ) (hm : 0 < m) (t r N k : ℕ)
    (indices attempts : List ℕ)
    (size start : List Bool → ℕ → ℕ)
    (q : List Bool → ℕ) (repValues : List Bool → List ℕ)
    (hpath : ValidPath (fun _ => m) t (fun _ => 0) 0 r indices attempts)
    (hfirstBudget : bitBudget (fun _ => m) t 0 r ≤ N)
    (hrep : ∀ pre : List Bool,
      pre.length = consumedBits (fun _ => m) 0 attempts →
      FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r pre indices attempts →
      ValidOutput (size pre) (start pre) 0 (q pre) (repValues pre))
    (hbudget : ∀ pre : List Bool,
      pre.length = consumedBits (fun _ => m) 0 attempts →
      FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r pre indices attempts →
      bitBudget (size pre) t 0 (q pre) ≤
        N - consumedBits (fun _ => m) 0 attempts)
    (hcount : ∀ pre : List Bool,
      pre.length = consumedBits (fun _ => m) 0 attempts →
      FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r pre indices attempts →
      outputCount (size pre) 0 (q pre) = k) :
    k * Nat.card {bits : List Bool // bits.length = N ∧
      FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r
        bits indices attempts ∧
      ∃ used charge,
        ClassTrace (size (bits.take (consumedBits (fun _ => m) 0 attempts)))
          t (start (bits.take (consumedBits (fun _ => m) 0 attempts))) 0
          (q (bits.take (consumedBits (fun _ => m) 0 attempts)))
          (bits.drop (consumedBits (fun _ => m) 0 attempts))
          (repValues (bits.take (consumedBits (fun _ => m) 0 attempts)))
          used charge false} ≤
      Nat.card {bits : List Bool // bits.length = N ∧
        FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r
          bits indices attempts} := by
  classical
  let u := consumedBits (fun _ => m) 0 attempts
  have hu : u ≤ N :=
    (ValidPath.consumedBits_le_budget (fun _ => m) t (fun _ => 0) hpath).trans
      hfirstBudget
  let P : List Bool → Prop := fun pre =>
    FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r pre indices attempts
  let Q : List Bool → List Bool → Prop := fun pre rest =>
    ∃ used charge,
      ClassTrace (size pre) t (start pre) 0 (q pre) rest
        (repValues pre) used charge false
  have hQ : ∀ pre : List Bool, pre.length = u → P pre →
      k * Nat.card {rest : List Bool // rest.length = N - u ∧ Q pre rest} ≤
        2 ^ (N - u) := by
    intro pre hlen hp
    have hclass := outputFiber_le_ideal_uniform (size pre) t (start pre)
      0 (q pre) (N - u) (repValues pre)
      (hbudget pre hlen hp) (hrep pre hlen hp)
    rw [hcount pre hlen hp] at hclass
    have hcard : Nat.card {rest : List Bool //
        rest.length = N - u ∧ Q pre rest} =
        (outputFiber (size pre) t (start pre) 0 (q pre)
          (N - u) (repValues pre)).card := by
      exact card_flatPredicate (N - u) (Q pre)
    rw [hcard]
    exact hclass
  have hbound := adaptiveConsumedPrefix_le N u k hu P Q hQ
  simpa only [P, Q, u,
    ← flatClassSuccess_iff_consumedPrefix (fun _ => m) t
      (fun _ => 0) 0 r _ indices attempts] using hbound

/-- The full initial stage sums the prefix-dependent class law over every
stopping vector and every concrete consumed bit prefix. -/
noncomputable def adaptiveInitialJointFiber
    (m t r N : ℕ) (indices : List ℕ)
    (size start : List ℕ → List Bool → ℕ → ℕ)
    (q : List ℕ → List Bool → ℕ)
    (repValues : List ℕ → List Bool → List ℕ) : Finset (FlatTape N) := by
  classical
  exact Finset.univ.filter fun tape =>
    ∃ attempts,
      FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r
        (flatBits tape) indices attempts ∧
      let pre := (flatBits tape).take
        (consumedBits (fun _ => m) 0 attempts)
      ∃ used charge,
        ClassTrace (size attempts pre) t (start attempts pre) 0
          (q attempts pre)
          ((flatBits tape).drop (consumedBits (fun _ => m) 0 attempts))
          (repValues attempts pre) used charge false

lemma adaptiveInitialJointFiber_le_ideal
    (m : ℕ) (hm : 0 < m) (t r N k : ℕ) (indices : List ℕ)
    (size start : List ℕ → List Bool → ℕ → ℕ)
    (q : List ℕ → List Bool → ℕ)
    (repValues : List ℕ → List Bool → List ℕ)
    (hindices : ValidOutput (fun _ => m) (fun _ => 0) 0 r indices)
    (hfirstBudget : bitBudget (fun _ => m) t 0 r ≤ N)
    (hrep : ∀ a ∈ attemptVectors t r, ∀ pre : List Bool,
      pre.length = consumedBits (fun _ => m) 0 a →
      FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r pre indices a →
      ValidOutput (size a pre) (start a pre) 0 (q a pre)
        (repValues a pre))
    (hbudget : ∀ a ∈ attemptVectors t r, ∀ pre : List Bool,
      pre.length = consumedBits (fun _ => m) 0 a →
      FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r pre indices a →
      bitBudget (size a pre) t 0 (q a pre) ≤
        N - consumedBits (fun _ => m) 0 a)
    (hcount : ∀ a ∈ attemptVectors t r, ∀ pre : List Bool,
      pre.length = consumedBits (fun _ => m) 0 a →
      FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r pre indices a →
      outputCount (size a pre) 0 (q a pre) = k) :
    m ^ r * k *
      (adaptiveInitialJointFiber m t r N indices size start q repValues).card
        ≤ 2 ^ N := by
  classical
  let J : List ℕ → Finset (FlatTape N) := fun a =>
    Finset.univ.filter fun tape =>
      FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r
        (flatBits tape) indices a ∧
      let pre := (flatBits tape).take (consumedBits (fun _ => m) 0 a)
      ∃ used charge,
        ClassTrace (size a pre) t (start a pre) 0 (q a pre)
          ((flatBits tape).drop (consumedBits (fun _ => m) 0 a))
          (repValues a pre) used charge false
  let K : List ℕ → Finset (FlatTape N) := fun a =>
    pathFiber (fun _ => m) t (fun _ => 0) 0 r N indices a
  have hsub (a : List ℕ) : J a ⊆ K a := by
    intro tape ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp ht).2.1⟩
  have hJdisj : ∀ a ∈ attemptVectors t r, ∀ b ∈ attemptVectors t r,
      a ≠ b → Disjoint (J a) (J b) := by
    intro a _ b _ hab
    exact (pathFiber_disjoint (fun _ => m) t (fun _ => 0)
      0 r N indices hab).mono (hsub a) (hsub b)
  have hper (a : List ℕ) (ha : a ∈ attemptVectors t r) :
      k * (J a).card ≤ (K a).card := by
    have hpath := ValidOutput.validPath_of_mem (fun _ => m) t
      (fun _ => 0) hindices a ha
    have h := adaptiveInitialPath_le_ideal m hm t r N k indices a
      (size a) (start a) (q a) (repValues a) hpath hfirstBudget
      (hrep a ha) (hbudget a ha) (hcount a ha)
    have hj : (J a).card = Nat.card {bits : List Bool //
        bits.length = N ∧
        FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r
          bits indices a ∧
        ∃ used charge,
          ClassTrace (size a (bits.take (consumedBits (fun _ => m) 0 a)))
            t (start a (bits.take (consumedBits (fun _ => m) 0 a))) 0
            (q a (bits.take (consumedBits (fun _ => m) 0 a)))
            (bits.drop (consumedBits (fun _ => m) 0 a))
            (repValues a (bits.take (consumedBits (fun _ => m) 0 a)))
            used charge false} := by
      exact (card_flatPredicate N (fun bits =>
        FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r
          bits indices a ∧
        ∃ used charge,
          ClassTrace
            (size a (bits.take (consumedBits (fun _ => m) 0 a)))
            t (start a (bits.take (consumedBits (fun _ => m) 0 a))) 0
            (q a (bits.take (consumedBits (fun _ => m) 0 a)))
            (bits.drop (consumedBits (fun _ => m) 0 a))
            (repValues a (bits.take (consumedBits (fun _ => m) 0 a)))
            used charge false)).symm
    have hk : (K a).card = Nat.card {bits : List Bool //
        bits.length = N ∧
        FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r
          bits indices a} := by
      exact (card_flatPredicate N (fun bits =>
        FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r
          bits indices a)).symm
    rw [hj, hk]
    exact h
  have hJunion : (attemptVectors t r).biUnion J =
      adaptiveInitialJointFiber m t r N indices size start q repValues := by
    ext tape
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
      true_and, J, adaptiveInitialJointFiber]
    constructor
    · rintro ⟨a, _, hfirst, hsecond⟩
      exact ⟨a, hfirst, hsecond⟩
    · rintro ⟨a, hfirst, hsecond⟩
      exact ⟨a, FlatClassSuccess.attempts_mem (fun _ => m) t
        (fun _ => 0) hfirst, hfirst, hsecond⟩
  have hsum : k *
      (adaptiveInitialJointFiber m t r N indices size start q repValues).card
        ≤ (outputFiber (fun _ => m) t (fun _ => 0) 0 r N indices).card := by
    rw [← hJunion, Finset.card_biUnion hJdisj,
      outputFiber_eq_biUnion (fun _ => m) t (fun _ => 0)
        0 r N indices hfirstBudget,
      Finset.card_biUnion, Finset.mul_sum]
    · exact Finset.sum_le_sum fun a ha => hper a ha
    · intro a ha b hb hab
      exact pathFiber_disjoint (fun _ => m) t (fun _ => 0)
        0 r N indices hab
  have hfirst := outputFiber_le_ideal_uniform (fun _ => m) t
    (fun _ => 0) 0 r N indices hfirstBudget hindices
  rw [outputCount_const m 0 r] at hfirst
  calc
    m ^ r * k *
        (adaptiveInitialJointFiber m t r N indices size start q repValues).card =
        m ^ r * (k *
          (adaptiveInitialJointFiber m t r N indices size start q repValues).card) := by ring
    _ ≤ m ^ r *
        (outputFiber (fun _ => m) t (fun _ => 0) 0 r N indices).card :=
      Nat.mul_le_mul_left _ hsum
    _ ≤ 2 ^ N := hfirst

end Lax457868Proofs.InitialFlatLaw
