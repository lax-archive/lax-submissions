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
open Lax457868Proofs.SamplerWeightedRetries
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.InitialSamplerChoice
open Lax457868Proofs.InitialSamplerAttempt
open Lax457868Proofs.InitialDrawSampleSource
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixMath
open Lax457868Proofs.ReusedOriginal.Construction.ReadKeys

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
      (∀ b ∈ activeVertices n I.activeB,
        (outcomeChoice A (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) r
          ⟨draw, reps⟩).representative b = mapped b) ∧
      draw = sourceOrderedDraw A m r I.domain I.henum values hlen := by
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
  refine ⟨draw, reps, hdrawSet, ?_, ?_, ?_, rfl⟩
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
    _hdrawRun, _hdrawInp, _hdrawFlag⟩ :=
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
  obtain ⟨draw, reps, hdrawSet, hmem, hprob, hrepresentative, _hordered⟩ :=
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

/-- A first source phase consumes a fixed prefix, then a read-free phase
computes the same partition state on every possible unread suffix. -/
lemma run_twoPhase_sameConsumedPrefix
    {B : ℕ} {first second : Com}
    {σ σd σd' σp σp' : Env}
    {K K' L L' : ℕ}
    (pre rest rest' : List ℕ)
    (hinput : σ.inp = pre ++ rest)
    (hdrawInput : σd.inp = rest)
    (hfirst : Run B first σ σd K)
    (hfirst' : Run B first {σ with inp := pre ++ rest'} σd' K')
    (hsecond : Run B second σd σp L)
    (hnoRead : σp.inp = σd.inp)
    (hsecond' : Run B second σd' σp' L') :
    σp' = {σp with inp := σd'.inp} := by
  have hdraw := run_same_consumedPrefix pre rest rest' hinput
    hdrawInput hfirst hfirst'
  rw [hdraw] at hsecond'
  have hpart := run_same_consumedPrefix [] σd.inp rest'
    (by simp) hnoRead hsecond (by simpa using hsecond')
  simpa [hdraw] using hpart

/-- Equality of partition arrays recovers equality of each live class label
or class size, while leaving irrelevant out-of-range function values free. -/
lemma arrOf_eq_on {n : ℕ} {f g : ℕ → ℕ}
    (h : arrOf n f = arrOf n g) (i : ℕ) (hi : i < n) :
    f i = g i := by
  have hf := getD_arrOf f hi
  have hg := getD_arrOf g hi
  exact hf.symm.trans ((congrArg (fun xs : List ℕ => xs.getD i 0) h).trans hg)

private lemma stoppedPrefix_cast {m m' u : ℕ} (heq : m = m')
    (hm : 0 < m) (i : Fin m) (pre : BitTape m u)
    (hp : stoppedEvent m hm u u i pre) :
    ∃ (i' : Fin m') (pre' : BitTape m' u) (hm' : 0 < m'),
      i'.val = i.val ∧ tapeBits pre' = tapeBits pre ∧
        stoppedEvent m' hm' u u i' pre' := by
  subst m'
  exact ⟨i, pre, hm, rfl, rfl, hp⟩

private lemma flatClassSuccess_congr_live
    (size size' start start' : ℕ → ℕ) (t : ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {values attempts : List ℕ},
      FlatClassSuccess size t start d r bits values attempts →
      (∀ j < r, size (d + j) = size' (d + j)) →
      (∀ j < r, start (d + j) = start' (d + j)) →
      FlatClassSuccess size' t start' d r bits values attempts
  | _, _, _, _, _, .done d bits, _, _ => by
      simpa using (FlatClassSuccess.done d bits)
  | _, _, _, _, _, .step (d := d) (r := r) (v := v) i pre rest hm hu hp hnext,
      hsize, hstart => by
      have hsd : size d = size' d := by simpa using hsize 0 (by omega)
      have hst : start d = start' d := by simpa using hstart 0 (by omega)
      have hsizeNext : ∀ j < r, size (d + 1 + j) = size' (d + 1 + j) := by
        intro j hj
        have h := hsize (j + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hstartNext : ∀ j < r, start (d + 1 + j) = start' (d + 1 + j) := by
        intro j hj
        have h := hstart (j + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hnext' := flatClassSuccess_congr_live size size' start start' t
        hnext hsizeNext hstartNext
      obtain ⟨i', pre', hm', hiVal, hpreBits, hp'⟩ :=
        stoppedPrefix_cast hsd hm i pre hp
      rw [hst, ← hiVal, ← hpreBits]
      exact FlatClassSuccess.step i' pre' rest hm' hu hp' hnext'

private lemma classTrace_success_congr_live
    (size size' start start' : ℕ → ℕ) (t d q : ℕ)
    (bits : List Bool) (values : List ℕ) (used charge : ℕ)
    (htrace : ClassTrace size t start d q bits values used charge false)
    (hsize : ∀ j < q, size (d + j) = size' (d + j))
    (hstart : ∀ j < q, start (d + j) = start' (d + j))
    (hbudget : bitBudget size' t d q ≤ bits.length) :
    ∃ used' charge',
      ClassTrace size' t start' d q bits values used' charge' false := by
  obtain ⟨attempts, hflat⟩ :=
    classTrace_success_to_flat size t start htrace rfl
  have hflat' := flatClassSuccess_congr_live size size' start start' t
    hflat hsize hstart
  obtain ⟨used', charge', htrace', _, _⟩ :=
    flatClassSuccess_to_classTrace size' t start' hflat' hbudget
  exact ⟨used', charge', htrace'⟩

def reinputInitialAttempt
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (bits : List Bool)
    (hbudget : r * t * Nat.clog 2 m + n * t * Nat.clog 2 n ≤ bits.length) :
    Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A := by
  refine { I with
    σ := {I.σ with inp := bits.map Bool.toNat ++ I.rest},
    bits := bits,
    hinput := rfl,
    hbudget := hbudget,
    hn := ?_, hQpow := ?_, hactiveBCount := ?_, hdrawModulus := ?_,
    hbatchTarget := ?_, hdrawCap := ?_, hkey0 := ?_, hdrawDomain := ?_,
    hsampleDraws := ?_, hsampleFlags := ?_, hord := ?_, hoff := ?_,
    htarget := ?_, hactiveB := ?_, hclassB := ?_, hclassSize := ?_,
    hmarkedCount := ?_, hstamp := ?_, htouched := ?_, hsplit := ?_,
    hrepB := ?_, hcount := ?_, hscratch := ?_, hrepClass := ?_ }
  all_goals simp only [Env.mk.injEq] <;> first
    | exact I.hn | exact I.hQpow | exact I.hactiveBCount
    | exact I.hdrawModulus | exact I.hbatchTarget | exact I.hdrawCap
    | exact I.hkey0 | exact I.hdrawDomain | exact I.hsampleDraws
    | exact I.hsampleFlags | exact I.hord | exact I.hoff
    | exact I.htarget | exact I.hactiveB | exact I.hclassB
    | exact I.hclassSize | exact I.hmarkedCount | exact I.hstamp
    | exact I.htouched | exact I.hsplit | exact I.hrepB
    | exact I.hcount | exact I.hscratch | exact I.hrepClass

private noncomputable def indicesOfOutcome
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r) : List ℕ :=
  List.ofFn fun j : Fin r =>
    ((prefixDomainEnumeration m I.domain A I.henum).symm (ω.1 j)).val

private lemma sourceOrderedDraw_indices_eq
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r)
    (values : List (Fin m)) (hlen : values.length = r)
    (hdraw : sourceOrderedDraw A m r I.domain I.henum values hlen = ω.1) :
    values.map Fin.val = indicesOfOutcome I ω := by
  apply List.ext_getElem
  · simp [hlen, indicesOfOutcome]
  · intro j hj hj'
    have hjr : j < r := by simpa [hlen] using hj
    let enum := prefixDomainEnumeration m I.domain A I.henum
    have hcard : m = A.card := prefixEnumerates_card m I.domain A I.henum
    let idx : Fin A.card := ⟨(values[j]'(by simpa [hlen] using hjr)).val,
      by simpa [← hcard] using (values[j]'(by simpa [hlen] using hjr)).isLt⟩
    have heq := congrArg (fun f : Fin r → A => f ⟨j, hjr⟩) hdraw
    change enum idx = ω.1 ⟨j, hjr⟩ at heq
    have heq' := congrArg enum.symm heq
    have heqVal := congrArg Fin.val heq'
    simpa [indicesOfOutcome, enum, idx] using heqVal

private lemma validOutput_const_of_bounded (m d : ℕ) :
    ∀ values : List ℕ,
      (∀ v ∈ values, v < m) →
      ValidOutput (fun _ => m) (fun _ => 0) d values.length values
  | [], _ => ValidOutput.done d
  | v :: vs, hbound => by
      have hv : v < m := hbound v (by simp)
      have htail : ∀ w ∈ vs, w < m := by
        intro w hw
        exact hbound w (by simp [hw])
      simpa using (ValidOutput.step (start := fun _ => 0)
        (i := ⟨v, hv⟩)
        (validOutput_const_of_bounded m (d + 1) vs htail))

private lemma indicesOfOutcome_valid
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r) :
    ValidOutput (fun _ => m) (fun _ => 0) 0 r
      (indicesOfOutcome I ω) := by
  have hcard : m = A.card := prefixEnumerates_card m I.domain A I.henum
  have hlength : (indicesOfOutcome I ω).length = r := by
    simp [indicesOfOutcome]
  have hbounded : ∀ v ∈ indicesOfOutcome I ω, v < m := by
    intro v hv
    simp only [indicesOfOutcome, List.mem_ofFn] at hv
    obtain ⟨j, rfl⟩ := hv
    simpa [hcard] using
      ((prefixDomainEnumeration m I.domain A I.henum).symm (ω.1 j)).isLt
  simpa [hlength] using
    validOutput_const_of_bounded m 0 (indicesOfOutcome I ω) hbounded

/-- One complete successful source execution, recording the exact first
consumed prefix and the partition arrays that determine the second modulus. -/
structure SourceInitialOutcomeWitness
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (bits : List Bool)
    (ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r) where
  σd : Env
  σp : Env
  σfinal : Env
  values : List (Fin m)
  valuesLength : values.length = r
  attempts : List ℕ
  used : ℕ
  q : ℕ
  label : ℕ → ℕ
  size : ℕ → ℕ
  sorted : ℕ → ℕ
  mapped : ℕ → ℕ
  repValues : List ℕ
  repUsed : ℕ
  repCharge : ℕ
  drawCost : ℕ
  partitionCost : ℕ
  attemptCost : ℕ
  drawFlat : FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r
    bits (values.map Fin.val) attempts
  consumed : consumedBits (fun _ => m) 0 attempts =
    used * Nat.clog 2 m
  drawRun : Run B initialDrawSampleSource
    ({I.σ with inp := bits.map Bool.toNat ++ I.rest}.setVar "attemptAccepted" 0)
    σd drawCost
  drawInput : σd.inp =
    (bits.drop (used * Nat.clog 2 m)).map Bool.toNat ++ I.rest
  partitionRun : Run B FullSamplePartition.fullSamplePartition σd σp partitionCost
  partitionInput : σp.inp = σd.inp
  partitionCount : σp.vars "classCount" = q
  partitionLabel : σp.arrs "classB" = arrOf n label
  partitionSize : σp.arrs "classSize" = arrOf n size
  classSizes : ClassSizes n q I.activeB label size
  occupied : LabelsOccupyPrefix q label (activeVertices n I.activeB)
  classifies : ∀ b ∈ activeVertices n I.activeB,
    ∀ b' ∈ activeVertices n I.activeB,
      (label b = label b' ↔
        trace (fun z => numericNeighborhood G z ∩ A)
          (drawSet A ω.1) b =
        trace (fun z => numericNeighborhood G z ∩ A)
          (drawSet A ω.1) b')
  sortedPrefix : ∀ i < (scanList I.activeB 0 n).length,
    sorted i = (bucketSort Q label (scanList I.activeB 0 n)).getD i 0
  classTrace : ClassTrace size t (classStart size) 0 q
    (bits.drop (used * Nat.clog 2 m)) repValues repUsed repCharge false
  attemptRun : Run B initialSamplerAttempt
    {I.σ with inp := bits.map Bool.toNat ++ I.rest} σfinal attemptCost
  attemptInput : σfinal.inp =
    (bits.drop (used * Nat.clog 2 m + repUsed)).map Bool.toNat ++ I.rest
  resultArray : σfinal.arrs "repB" = arrOf n mapped
  orderedDraw : sourceOrderedDraw A m r I.domain I.henum values
    valuesLength = ω.1
  formula : ∀ b ∈ activeVertices n I.activeB,
    mapped b = writeClassReps sorted I.repClass 0 repValues (label b)
  representative : ∀ b ∈ activeVertices n I.activeB,
    (outcomeChoice A (activeVertices n I.activeB)
      (fun z => numericNeighborhood G z ∩ A) r ω).representative b = mapped b

/-- Finite event for one exact successful abstract outcome of the executed
initial sampler on a uniformly chosen length-`N` flat tape. -/
noncomputable def sourceInitialOutcomeFiber
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r) :
    Finset (FlatTape I.bits.length) := by
  classical
  exact Finset.univ.filter fun tape =>
    Nonempty (SourceInitialOutcomeWitness I (flatBits tape) ω)

lemma initialSamplerAttempt_run_sourceOutcome
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A) :
    ∃ σ' : Env, ∃ attemptCost : ℕ,
      Run B initialSamplerAttempt I.σ σ' attemptCost ∧
      (σ'.vars "batchFailed" = 0 → σ'.vars "repFailed" = 0 →
        ∃ ω : InitialOutcome A (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) r,
          (flatBitsEquiv I.bits.length).symm ⟨I.bits, rfl⟩ ∈
            sourceInitialOutcomeFiber I ω) := by
  classical
  obtain ⟨σd, σ', tape, tail, values, used, drawFailed, stageCost,
    hbits, hdrawTrace, hrun, _haccepted, _hn, _hqpow, hbatchFailed,
    _harrFrame, _hvarFrame, _hdrawFailure, hdrawSuccess,
    hdrawRun, hdrawInp, _hdrawFlag⟩ :=
      Lax457868Proofs.InitialSamplerAttempt.initialSamplerAttempt_run_bits I
  let attemptCost :=
    2 + initialDrawSampleCost n m used
      (values.length + if drawFailed then 1 else 0)
      values.length drawFailed +
      (if drawFailed then 5 else 4 + stageCost)
  refine ⟨σ', attemptCost, hrun, ?_⟩
  intro hbatchOK hrepOK
  have hdrawOK : drawFailed = false := by
    cases drawFailed with
    | false => rfl
    | true => simp [hbatchFailed] at hbatchOK
  obtain ⟨W, sampleOrd, sampleCount, σp, q, label, size, xs, sorted,
    repValues, repUsed, repCharge, repFailed, hW, hWA, _hWcard,
    hlen, _hprefix, hpartition, hsizes, hoccupied, hclasses,
    _hselection, _hnFinal, _hqpowFinal, _hsampleCount, _hclassB,
    _hclassSize, _hord, hnodup, hxs, hclass, _hrepUsedLe,
    hrepFailedVal, _hrepFailure, _hsampleFlags, hinpSource,
    hrepSuccess, _hcost, hsourceCert⟩ := hdrawSuccess hdrawOK
  have hrepFalse : repFailed = false := by
    cases repFailed with
    | false => rfl
    | true => simp [hrepFailedVal] at hrepOK
  obtain ⟨mapped, hmappedArr, _hvFinal, hformulaSource, hrepClass⟩ :=
    hrepSuccess hrepFalse
  rcases hsourceCert with
    ⟨_hclassCountFinal, _hxsLen, hxsScan, hqP,
      hlabelP, hsizeP, hinP, hsorted, _hRI⟩
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
  obtain ⟨draw, reps, hdrawSet, _hmem, _hprob, hrepresentative, hordered⟩ :=
    initialSource_success_jointFiber I tape tail values used hbits
      (by simpa [hdrawOK] using hdrawTrace) W hW hWA hlen
      q label size sorted repValues repUsed repCharge
      (by simpa [hrepFalse] using hclass) hsizes hoccupied
      hclasses mapped hrepC hrepLabel hformula
  obtain ⟨charge, hdrawClass⟩ :=
    drawTrace_to_classTrace m I.hmPos t 0
      (by simpa [hdrawOK] using hdrawTrace)
  have hdrawClass' := classTrace_append (fun _ => m) t
    (fun _ => 0) hdrawClass tail
  have hfirstBudget : bitBudget (fun _ => m) t 0 r ≤ I.bits.length := by
    rw [constant_bitBudget]
    exact (Nat.le_add_right _ _).trans I.hbudget
  have hdrawClassBits : ClassTrace (fun _ => m) t (fun _ => 0) 0 r
      I.bits (values.map Fin.val) (used * Nat.clog 2 m) charge false := by
    simpa [hbits, tapeBits] using hdrawClass'
  obtain ⟨attempts, hflat, hconsumed⟩ :=
    classTrace_success_flat_used (fun _ => m) t (fun _ => 0)
      hdrawClassBits hfirstBudget
  have hclassifies : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace (fun z => numericNeighborhood G z ∩ A)
          (drawSet A draw) b =
        trace (fun z => numericNeighborhood G z ∩ A)
          (drawSet A draw) b') := by
    intro b hb b' hb'
    rw [hdrawSet, restrictedNeighborhood_trace_eq _ hWA,
      restrictedNeighborhood_trace_eq _ hWA]
    exact hclasses b hb b' hb'
  let ω : InitialOutcome A C
      (fun b => numericNeighborhood G b ∩ A) r := ⟨draw, reps⟩
  refine ⟨ω, ?_⟩
  simp only [sourceInitialOutcomeFiber, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hflatBits : flatBits ((flatBitsEquiv I.bits.length).symm
      ⟨I.bits, rfl⟩) = I.bits :=
    congrArg Subtype.val ((flatBitsEquiv I.bits.length).apply_symm_apply _)
  rw [hflatBits]
  change Nonempty (SourceInitialOutcomeWitness I I.bits ω)
  have hinputEnv : {I.σ with inp := I.bits.map Bool.toNat ++ I.rest} =
      I.σ := by
    rw [← I.hinput]
  refine ⟨{
    σd := σd, σp := σp, σfinal := σ', values := values,
    valuesLength := hlen, attempts := attempts, used := used,
    q := q, label := label, size := size, sorted := sorted,
    mapped := mapped, repValues := repValues,
    repUsed := repUsed, repCharge := repCharge,
    drawCost := initialDrawSampleCost n m used values.length values.length false,
    partitionCost := FullSamplePartition.fullSamplePartitionCost x sampleOrd n sampleCount,
    attemptCost := attemptCost,
    drawFlat := hflat, consumed := hconsumed,
    drawRun := by simpa [hinputEnv, hdrawOK] using hdrawRun,
    drawInput := hdrawInp,
    partitionRun := hpartition, partitionInput := hinP,
    partitionCount := hqP, partitionLabel := hlabelP,
    partitionSize := hsizeP, classSizes := hsizes,
    occupied := hoccupied, classifies := hclassifies,
    sortedPrefix := by simpa [hxsScan] using hsorted,
    classTrace := by simpa [hrepFalse] using hclass,
    attemptRun := by simpa [hinputEnv] using hrun,
    attemptInput := hinpSource,
    resultArray := hmappedArr, orderedDraw := hordered.symm,
    formula := hformula, representative := hrepresentative
  }⟩

lemma SourceInitialOutcomeWitness.outputCount_eq_ideal
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    {I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A}
    {bits : List Bool}
    {ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r}
    (w : SourceInitialOutcomeWitness I bits ω) :
    outputCount w.size 0 w.q =
      Fintype.card (RepChoices A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) ω.1) := by
  have hrange : ∀ b ∈ activeVertices n I.activeB, w.label b < w.q := by
    intro b hb
    obtain ⟨hbn, hactive⟩ := mem_activeVertices.mp hb
    exact w.classSizes.1 b hbn hactive
  exact (repChoices_card_eq_outputCount ω.1 w.label w.size
    hrange w.occupied w.classifies w.classSizes.2).symm

lemma SourceInitialOutcomeWitness.partition_eq_of_consumedPrefix
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    {I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A}
    {bits bits' : List Bool}
    {ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r}
    (w : SourceInitialOutcomeWitness I bits ω)
    (w' : SourceInitialOutcomeWitness I bits' ω)
    (hattempts : w.attempts = w'.attempts)
    (hprefix : bits.take (consumedBits (fun _ => m) 0 w.attempts) =
      bits'.take (consumedBits (fun _ => m) 0 w.attempts)) :
    w'.σp = {w.σp with inp := w'.σd.inp} := by
  let u := consumedBits (fun _ => m) 0 w.attempts
  let pre := (bits.take u).map Bool.toNat
  let rest := (bits.drop u).map Bool.toNat ++ I.rest
  let rest' := (bits'.drop u).map Bool.toNat ++ I.rest
  let σ₀ := {I.σ with inp := bits.map Bool.toNat ++ I.rest}.setVar
    "attemptAccepted" 0
  let σ₀' := {I.σ with inp := bits'.map Bool.toNat ++ I.rest}.setVar
    "attemptAccepted" 0
  have hsplit (ys : List Bool) :
      ys.map Bool.toNat ++ I.rest =
        (ys.take u).map Bool.toNat ++
          ((ys.drop u).map Bool.toNat ++ I.rest) := by
    calc
      ys.map Bool.toNat ++ I.rest =
          ((ys.map Bool.toNat).take u ++
            (ys.map Bool.toNat).drop u) ++ I.rest := by
            rw [List.take_append_drop]
      _ = _ := by
        rw [List.map_take, List.map_drop, List.append_assoc]
  have hinput : σ₀.inp = pre ++ rest := by
    change bits.map Bool.toNat ++ I.rest = _
    exact hsplit bits
  have houtput : w.σd.inp = rest := by
    rw [w.drawInput, ← w.consumed]
  have hσ₀' : σ₀' = {σ₀ with inp := pre ++ rest'} := by
    have hpre' : (bits'.take u).map Bool.toNat = pre := by
      exact congrArg (List.map Bool.toNat) hprefix.symm
    have hinp' : bits'.map Bool.toNat ++ I.rest = pre ++ rest' := by
      rw [hsplit bits', hpre']
    simp only [σ₀, σ₀', Env.setVar]
    rw [hinp']
  have hdrawRun' : Run B initialDrawSampleSource
      {σ₀ with inp := pre ++ rest'} w'.σd w'.drawCost := by
    rw [← hσ₀']
    exact w'.drawRun
  have hpart := run_twoPhase_sameConsumedPrefix pre rest rest'
    hinput houtput w.drawRun hdrawRun' w.partitionRun
    w.partitionInput w'.partitionRun
  exact hpart

lemma SourceInitialOutcomeWitness.livePartition_eq_of_consumedPrefix
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    {I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A}
    {bits bits' : List Bool}
    {ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r}
    (w : SourceInitialOutcomeWitness I bits ω)
    (w' : SourceInitialOutcomeWitness I bits' ω)
    (hattempts : w.attempts = w'.attempts)
    (hprefix : bits.take (consumedBits (fun _ => m) 0 w.attempts) =
      bits'.take (consumedBits (fun _ => m) 0 w.attempts)) :
    w.q = w'.q ∧
      (∀ b < n, w.label b = w'.label b) ∧
      (∀ d < n, w.size d = w'.size d) := by
  have hp := w.partition_eq_of_consumedPrefix w' hattempts hprefix
  have hvars : w.σp.vars = w'.σp.vars := by rw [hp]
  have harrs : w.σp.arrs = w'.σp.arrs := by rw [hp]
  have hq : w.q = w'.q := by
    calc
      w.q = w.σp.vars "classCount" := w.partitionCount.symm
      _ = w'.σp.vars "classCount" := congrFun hvars _
      _ = w'.q := w'.partitionCount
  have hlabelArr : arrOf n w.label = arrOf n w'.label := by
    calc
      arrOf n w.label = w.σp.arrs "classB" := w.partitionLabel.symm
      _ = w'.σp.arrs "classB" := congrFun harrs _
      _ = arrOf n w'.label := w'.partitionLabel
  have hsizeArr : arrOf n w.size = arrOf n w'.size := by
    calc
      arrOf n w.size = w.σp.arrs "classSize" := w.partitionSize.symm
      _ = w'.σp.arrs "classSize" := congrFun harrs _
      _ = arrOf n w'.size := w'.partitionSize
  exact ⟨hq, fun b hb => arrOf_eq_on hlabelArr b hb,
    fun d hd => arrOf_eq_on hsizeArr d hd⟩

private lemma classStart_congr_live (size size' : ℕ → ℕ) (q : ℕ)
    (hsize : ∀ d < q, size d = size' d) :
    ∀ d ≤ q, classStart size d = classStart size' d := by
  intro d hd
  induction d with
  | zero => rfl
  | succ d ih =>
      have hdq : d < q := by omega
      simpa [classStart, ih (by omega), hsize d hdq]

private lemma SourceInitialOutcomeWitness.q_le_n
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    {I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A}
    {bits : List Bool}
    {ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r}
    (w : SourceInitialOutcomeWitness I bits ω) : w.q ≤ n := by
  have hrange : ∀ b ∈ activeVertices n I.activeB,
      w.label b < w.q := by
    intro b hb
    obtain ⟨hbn, hactive⟩ := mem_activeVertices.mp hb
    exact w.classSizes.1 b hbn hactive
  exact (occupied_classCount_le_card (activeVertices n I.activeB)
    w.label w.q hrange w.occupied).trans
      (activeVertices_card_le n I.activeB)

private lemma SourceInitialOutcomeWitness.sortedPrefix_eq_of_livePartition
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    {I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A}
    {bits bits' : List Bool}
    {ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r}
    (w : SourceInitialOutcomeWitness I bits ω)
    (w' : SourceInitialOutcomeWitness I bits' ω)
    (hlabel : ∀ b < n, w.label b = w'.label b) :
    ∀ i < (scanList I.activeB 0 n).length,
      w.sorted i = w'.sorted i := by
  let xs := scanList I.activeB 0 n
  have hbucket : bucketSort Q w.label xs =
      bucketSort Q w'.label xs := by
    unfold bucketSort
    congr 1
    funext d
    apply List.filter_congr
    intro b hb
    have hbn : b < n := by
      simpa [xs] using (scanList_mem_range hb)
    simp [hlabel b hbn]
  intro i hi
  calc
    w.sorted i = (bucketSort Q w.label xs).getD i 0 := w.sortedPrefix i hi
    _ = (bucketSort Q w'.label xs).getD i 0 := by rw [hbucket]
    _ = w'.sorted i := (w'.sortedPrefix i hi).symm

private lemma validOutput_congr_live
    (size size' start start' : ℕ → ℕ) :
    ∀ {d q : ℕ} {values : List ℕ},
      ValidOutput size start d q values →
      (∀ j < q, size (d + j) = size' (d + j)) →
      (∀ j < q, start (d + j) = start' (d + j)) →
      ValidOutput size' start' d q values
  | _, _, _, .done d, _, _ => ValidOutput.done d
  | _, _, _, .step (d := d) (r := r) i hnext, hsize, hstart => by
      have hsd : size d = size' d := by simpa using hsize 0 (by omega)
      have hst : start d = start' d := by simpa using hstart 0 (by omega)
      have hsizeNext : ∀ j < r, size (d + 1 + j) = size' (d + 1 + j) := by
        intro j hj
        have h := hsize (j + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hstartNext : ∀ j < r, start (d + 1 + j) = start' (d + 1 + j) := by
        intro j hj
        have h := hstart (j + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      have hnext' := validOutput_congr_live size size' start start'
        hnext hsizeNext hstartNext
      let i' : Fin (size' d) := Fin.cast hsd i
      have hi : i'.val = i.val := rfl
      simpa [hst, hi] using (ValidOutput.step i' hnext')

lemma SourceInitialOutcomeWitness.repValues_eq_of_consumedPrefix
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    {I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A}
    {bits bits' : List Bool}
    {ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r}
    (w : SourceInitialOutcomeWitness I bits ω)
    (w' : SourceInitialOutcomeWitness I bits' ω)
    (hattempts : w.attempts = w'.attempts)
    (hprefix : bits.take (consumedBits (fun _ => m) 0 w.attempts) =
      bits'.take (consumedBits (fun _ => m) 0 w.attempts)) :
    w.repValues = w'.repValues := by
  classical
  let C := activeVertices n I.activeB
  let xs := scanList I.activeB 0 n
  obtain ⟨hq, hlabel, hsize⟩ :=
    w.livePartition_eq_of_consumedPrefix w' hattempts hprefix
  have hsorted := w.sortedPrefix_eq_of_livePartition w' hlabel
  have hqN : w.q ≤ n := w.q_le_n
  have hrange : ∀ b ∈ C, w.label b < w.q := by
    intro b hb
    obtain ⟨hbn, hactive⟩ := mem_activeVertices.mp hb
    exact w.classSizes.1 b hbn hactive
  have hsizes : ∀ d < w.q,
      w.size d = classMultiplicity w.label C d := w.classSizes.2
  have hxsNodup : xs.Nodup := scanList_nodup I.activeB 0 n
  have hxsSet : xs.toFinset = C := by
    simpa [xs, C, SamplePacking.flaggedVertices] using
      SamplePacking.scanList_toFinset I.activeB n
  have hxsLen : xs.length = C.card := by
    rw [← hxsSet, List.toFinset_card_of_nodup hxsNodup]
  have hrepA : ValidOutput w.size (classStart w.size) 0 w.q
      w.repValues := by
    obtain ⟨attempts, hflat⟩ := classTrace_success_to_flat
      w.size t (classStart w.size) w.classTrace rfl
    exact ValidPath.validOutput w.size t (classStart w.size)
      (FlatClassSuccess.validPath w.size t (classStart w.size) hflat)
  have hrepB : ValidOutput w'.size (classStart w'.size) 0 w'.q
      w'.repValues := by
    obtain ⟨attempts, hflat⟩ := classTrace_success_to_flat
      w'.size t (classStart w'.size) w'.classTrace rfl
    exact ValidPath.validOutput w'.size t (classStart w'.size)
      (FlatClassSuccess.validPath w'.size t (classStart w'.size) hflat)
  have hrepB' : ValidOutput w'.size (classStart w'.size) 0 w.q
      w'.repValues := by simpa [hq] using hrepB
  have hsizeLive : ∀ d < w.q, w'.size d = w.size d := by
    intro d hd
    exact (hsize d (hd.trans_le hqN)).symm
  have hstartLive : ∀ d < w.q,
      classStart w'.size d = classStart w.size d := by
    intro d hd
    exact classStart_congr_live w'.size w.size w.q hsizeLive d
      (Nat.le_of_lt hd)
  have hrepBcanonical : ValidOutput w.size (classStart w.size) 0
      w.q w'.repValues :=
    validOutput_congr_live w'.size w.size
      (classStart w'.size) (classStart w.size) hrepB'
      (by simpa using hsizeLive) (by simpa using hstartLive)
  obtain ⟨hlenB, hboundB⟩ :=
    validOutput_length_and_bound w'.size hrepB'
  have hcapB : classStart w'.size w.q = C.card := by
    have hrangeB : ∀ b ∈ C, w'.label b < w'.q := by
      intro b hb
      obtain ⟨hbn, hactive⟩ := mem_activeVertices.mp hb
      exact w'.classSizes.1 b hbn hactive
    simpa [hq] using
      classStart_eq_card_of_sizes C w'.label w'.size w'.q
        hrangeB w'.classSizes.2
  have hmapA : ∀ b ∈ C,
      w.mapped b = writeClassReps w.sorted I.repClass 0
        w.repValues (w.label b) := w.formula
  have hmapB : ∀ b ∈ C,
      w.mapped b = writeClassReps w.sorted I.repClass 0
        w'.repValues (w.label b) := by
    intro b hb
    have hbn : b < n := (mem_activeVertices.mp hb).1
    have hlabelB : w.label b = w'.label b := hlabel b hbn
    have hdq : w'.label b < w'.q := by
      obtain ⟨_, hactive⟩ := mem_activeVertices.mp hb
      exact w'.classSizes.1 b hbn hactive
    have hindex : w'.label b < w'.repValues.length := by omega
    have hpos : w'.repValues[w'.label b] < xs.length := by
      rw [hxsLen, ← hcapB]
      simpa only [Nat.zero_add] using
        hboundB _ (List.getElem_mem hindex)
    have hsortedAt := hsorted w'.repValues[w'.label b] hpos
    have hlookup' := writeClassReps_at w'.sorted I.repClass 0
      w'.repValues (w'.label b) hindex
    have hlookup := writeClassReps_at w.sorted I.repClass 0
      w'.repValues (w'.label b) hindex
    calc
      w.mapped b = w'.mapped b :=
        (w.representative b hb).symm.trans (w'.representative b hb)
      _ = writeClassReps w'.sorted I.repClass 0 w'.repValues
            (w'.label b) := w'.formula b hb
      _ = w'.sorted w'.repValues[w'.label b] := by simpa using hlookup'
      _ = w.sorted w'.repValues[w'.label b] := hsortedAt.symm
      _ = writeClassReps w.sorted I.repClass 0 w'.repValues
            (w.label b) := by simpa [hlabelB] using hlookup.symm
  exact numericRepValues_unique_of_mapped C w.label w.size w.sorted
    I.repClass w.q xs Q hrange w.occupied hsizes hxsNodup
    hxsSet hxsLen w.sortedPrefix (hqN.trans I.hQle)
    w.repValues w'.repValues hrepA hrepBcanonical
    w.mapped hmapA hmapB

private noncomputable def sourcePathFiber
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r)
    (a : List ℕ) : Finset (FlatTape I.bits.length) := by
  classical
  exact Finset.univ.filter fun tape =>
    ∃ w : SourceInitialOutcomeWitness I (flatBits tape) ω,
      w.attempts = a

private lemma sourceInitialOutcomeFiber_eq_biUnion
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r) :
    sourceInitialOutcomeFiber I ω =
      (attemptVectors t r).biUnion (sourcePathFiber I ω) := by
  classical
  ext tape
  simp only [sourceInitialOutcomeFiber, sourcePathFiber,
    Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion]
  constructor
  · intro hw
    let w := Classical.choice hw
    exact ⟨w.attempts,
      FlatClassSuccess.attempts_mem (fun _ => m) t (fun _ => 0)
        w.drawFlat, w, rfl⟩
  · rintro ⟨a, _, w, _⟩
    exact ⟨w⟩

private lemma SourceInitialOutcomeWitness.samePrefix_classTrace
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    {I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A}
    {bits₀ bits : List Bool}
    {ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r}
    (w₀ : SourceInitialOutcomeWitness I bits₀ ω)
    (w : SourceInitialOutcomeWitness I bits ω)
    (hattempts : w₀.attempts = w.attempts)
    (hprefix : bits₀.take (consumedBits (fun _ => m) 0 w₀.attempts) =
      bits.take (consumedBits (fun _ => m) 0 w₀.attempts))
    (hlen : bits.length = I.bits.length) :
    ∃ used charge,
      ClassTrace w₀.size t (classStart w₀.size) 0 w₀.q
        (bits.drop (consumedBits (fun _ => m) 0 w₀.attempts))
        w₀.repValues used charge false := by
  obtain ⟨hq, _hlabel, hsize⟩ :=
    w₀.livePartition_eq_of_consumedPrefix w hattempts hprefix
  have hrepValues := w₀.repValues_eq_of_consumedPrefix w
    hattempts hprefix
  have hqN : w₀.q ≤ n := w₀.q_le_n
  have hsizeLive : ∀ d < w₀.q, w.size d = w₀.size d := by
    intro d hd
    exact (hsize d (hd.trans_le hqN)).symm
  have hstartLive : ∀ d < w₀.q,
      classStart w.size d = classStart w₀.size d := by
    intro d hd
    exact classStart_congr_live w.size w₀.size w₀.q hsizeLive d
      (Nat.le_of_lt hd)
  let u := consumedBits (fun _ => m) 0 w₀.attempts
  have hused : w.used * Nat.clog 2 m = u := by
    rw [← w.consumed, ← hattempts]
  have hclass : ClassTrace w.size t (classStart w.size) 0 w₀.q
      (bits.drop u) w₀.repValues w.repUsed w.repCharge false := by
    simpa [hused, hq, hrepValues] using w.classTrace
  have hfirstBudget : bitBudget (fun _ => m) t 0 r ≤ I.bits.length := by
    rw [constant_bitBudget]
    exact (Nat.le_add_right _ _).trans I.hbudget
  have hconsumed : u ≤ bitBudget (fun _ => m) t 0 r :=
    ValidPath.consumedBits_le_budget (fun _ => m) t (fun _ => 0)
      (FlatClassSuccess.validPath (fun _ => m) t (fun _ => 0)
        w₀.drawFlat)
  have htotal := initialSource_jointBudget I w₀.q w₀.label
    w₀.size w₀.classSizes w₀.occupied
  have hbudget : bitBudget w₀.size t 0 w₀.q ≤
      (bits.drop u).length := by
    simp only [List.length_drop, hlen]
    omega
  exact classTrace_success_congr_live w.size w₀.size
    (classStart w.size) (classStart w₀.size) t 0 w₀.q
    (bits.drop u) w₀.repValues w.repUsed w.repCharge hclass
    (by simpa using hsizeLive) (by simpa using hstartLive)
    hbudget

private lemma sourcePrefix_suffix_count_le
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r)
    (a : List ℕ) (ha : a ∈ attemptVectors t r)
    (pre : List Bool)
    (hpre : pre.length = consumedBits (fun _ => m) 0 a) :
    let u := consumedBits (fun _ => m) 0 a
    let k := Fintype.card (RepChoices A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) ω.1)
    k * Nat.card {rest : List Bool //
      rest.length = I.bits.length - u ∧
        ∃ w : SourceInitialOutcomeWitness I (pre ++ rest) ω,
          w.attempts = a} ≤ 2 ^ (I.bits.length - u) := by
  classical
  dsimp only
  let u := consumedBits (fun _ => m) 0 a
  let N := I.bits.length
  let k := Fintype.card (RepChoices A (activeVertices n I.activeB)
    (fun b => numericNeighborhood G b ∩ A) ω.1)
  let F : Finset (FlatTape (N - u)) :=
    Finset.univ.filter fun tail =>
      ∃ w : SourceInitialOutcomeWitness I (pre ++ flatBits tail) ω,
        w.attempts = a
  have hcardF : Nat.card {rest : List Bool // rest.length = N - u ∧
      ∃ w : SourceInitialOutcomeWitness I (pre ++ rest) ω,
        w.attempts = a} = F.card := by
    exact card_flatPredicate (N - u) _
  rw [hcardF]
  by_cases hnonempty : F.Nonempty
  · obtain ⟨tail₀, htail₀⟩ := hnonempty
    obtain ⟨w₀, hw₀⟩ := (Finset.mem_filter.mp htail₀).2
    have hindices := indicesOfOutcome_valid I ω
    have hpath := ValidOutput.validPath_of_mem (fun _ => m) t
      (fun _ => 0) hindices a ha
    have hfirstBudget : bitBudget (fun _ => m) t 0 r ≤ N := by
      rw [constant_bitBudget]
      exact (Nat.le_add_right _ _).trans I.hbudget
    have huBudget : u ≤ bitBudget (fun _ => m) t 0 r :=
      ValidPath.consumedBits_le_budget (fun _ => m) t (fun _ => 0)
        hpath
    have htotal := initialSource_jointBudget I w₀.q w₀.label
      w₀.size w₀.classSizes w₀.occupied
    have hbudget : bitBudget w₀.size t 0 w₀.q ≤ N - u := by
      omega
    have hrep : ValidOutput w₀.size (classStart w₀.size) 0
        w₀.q w₀.repValues := by
      obtain ⟨attempts, hflat⟩ := classTrace_success_to_flat
        w₀.size t (classStart w₀.size) w₀.classTrace rfl
      exact ValidPath.validOutput w₀.size t (classStart w₀.size)
        (FlatClassSuccess.validPath w₀.size t (classStart w₀.size) hflat)
    have hsubset : F ⊆ outputFiber w₀.size t (classStart w₀.size)
        0 w₀.q (N - u) w₀.repValues := by
      intro tail ht
      obtain ⟨w, hw⟩ := (Finset.mem_filter.mp ht).2
      have hprefix₀ : (pre ++ flatBits tail₀).take u = pre := by
        simp [hpre, u]
      have hprefix : (pre ++ flatBits tail).take u = pre := by
        simp [hpre, u]
      have hbitsLen : (pre ++ flatBits tail).length = N := by
        simp [hpre, flatBits_length, u]
        omega
      have hsamePrefix :
          (pre ++ flatBits tail₀).take
              (consumedBits (fun _ => m) 0 w₀.attempts) =
            (pre ++ flatBits tail).take
              (consumedBits (fun _ => m) 0 w₀.attempts) := by
        rw [hw₀]
        exact hprefix₀.trans hprefix.symm
      have hclass := w₀.samePrefix_classTrace w
        (hw₀.trans hw.symm) hsamePrefix hbitsLen
      have hrest : (pre ++ flatBits tail).drop u = flatBits tail := by
        simp [hpre, u]
      have hrest' :
          (pre ++ flatBits tail).drop
              (consumedBits (fun _ => m) 0 w₀.attempts) = flatBits tail := by
        rw [hw₀]
        exact hrest
      rw [hrest'] at hclass
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclass⟩
    have hclassBound := outputFiber_le_ideal_uniform w₀.size t
      (classStart w₀.size) 0 w₀.q (N - u) w₀.repValues
      hbudget hrep
    rw [w₀.outputCount_eq_ideal] at hclassBound
    exact (Nat.mul_le_mul_left k (Finset.card_le_card hsubset)).trans
      hclassBound
  · have hF : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    simp [hF]

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

private lemma sourcePathFiber_le_firstPath
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r)
    (a : List ℕ) (ha : a ∈ attemptVectors t r) :
    Fintype.card (RepChoices A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) ω.1) *
      (sourcePathFiber I ω a).card ≤
    (pathFiber (fun _ => m) t (fun _ => 0) 0 r
      I.bits.length (indicesOfOutcome I ω) a).card := by
  classical
  let N := I.bits.length
  let u := consumedBits (fun _ => m) 0 a
  let k := Fintype.card (RepChoices A (activeVertices n I.activeB)
    (fun b => numericNeighborhood G b ∩ A) ω.1)
  let P : List Bool → Prop := fun pre =>
    FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r
      pre (indicesOfOutcome I ω) a
  let R : List Bool → List Bool → Prop := fun pre rest =>
    ∃ w : SourceInitialOutcomeWitness I (pre ++ rest) ω,
      w.attempts = a
  have hfirstBudget : bitBudget (fun _ => m) t 0 r ≤ N := by
    rw [constant_bitBudget]
    exact (Nat.le_add_right _ _).trans I.hbudget
  have hpath := ValidOutput.validPath_of_mem (fun _ => m) t
    (fun _ => 0) (indicesOfOutcome_valid I ω) a ha
  have hu : u ≤ N :=
    (ValidPath.consumedBits_le_budget (fun _ => m) t
      (fun _ => 0) hpath).trans hfirstBudget
  have hQ : ∀ pre : List Bool, pre.length = u → P pre →
      k * Nat.card {rest : List Bool // rest.length = N - u ∧
        R pre rest} ≤ 2 ^ (N - u) := by
    intro pre hpre _
    exact sourcePrefix_suffix_count_le I ω a ha pre hpre
  have hbound := adaptiveConsumedPrefix_le N u k hu P R hQ
  have hsource : (sourcePathFiber I ω a).card =
      Nat.card {bits : List Bool // bits.length = N ∧
        P (bits.take u) ∧ R (bits.take u) (bits.drop u)} := by
    rw [card_flatPredicate N]
    congr 1
    ext tape
    simp only [sourcePathFiber, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨w, hw⟩
      have hindices := sourceOrderedDraw_indices_eq I ω
        w.values w.valuesLength w.orderedDraw
      have hdraw : FlatClassSuccess (fun _ => m) t (fun _ => 0) 0 r
          (flatBits tape) (indicesOfOutcome I ω) a := by
        simpa [hindices, hw] using w.drawFlat
      have hprefix : P ((flatBits tape).take u) := by
        exact (flatClassSuccess_iff_consumedPrefix (fun _ => m) t
          (fun _ => 0) 0 r (flatBits tape) (indicesOfOutcome I ω) a).mp
          hdraw
      refine ⟨hprefix, ?_⟩
      change ∃ v : SourceInitialOutcomeWitness I
        ((flatBits tape).take u ++ (flatBits tape).drop u) ω,
          v.attempts = a
      rw [List.take_append_drop]
      exact ⟨w, hw⟩
    · rintro ⟨_, w, hw⟩
      change ∃ v : SourceInitialOutcomeWitness I (flatBits tape) ω,
        v.attempts = a
      have hrebuild : (flatBits tape).take u ++
          (flatBits tape).drop u = flatBits tape :=
        List.take_append_drop u (flatBits tape)
      have hR : ∃ v : SourceInitialOutcomeWitness I
          ((flatBits tape).take u ++ (flatBits tape).drop u) ω,
            v.attempts = a := ⟨w, hw⟩
      rw [hrebuild] at hR
      exact hR
  have hfirst : Nat.card {bits : List Bool // bits.length = N ∧
      P (bits.take u)} =
      (pathFiber (fun _ => m) t (fun _ => 0) 0 r N
        (indicesOfOutcome I ω) a).card := by
    rw [card_flatPredicate N]
    congr 1
    ext tape
    simp only [pathFiber, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact (flatClassSuccess_iff_consumedPrefix (fun _ => m) t
      (fun _ => 0) 0 r (flatBits tape) (indicesOfOutcome I ω) a).symm
  rw [← hsource, hfirst] at hbound
  exact hbound

/-- The actual successful source event for one abstract outcome is bounded
by the full ideal draw-and-representative denominator. The class sizes used
for a tape are obtained from its executed sample partition. -/
lemma sourceInitialOutcomeFiber_le_ideal
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r) :
    m ^ r * Fintype.card (RepChoices A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) ω.1) *
      (sourceInitialOutcomeFiber I ω).card ≤ 2 ^ I.bits.length := by
  classical
  let indices := indicesOfOutcome I ω
  let k := Fintype.card (RepChoices A (activeVertices n I.activeB)
    (fun b => numericNeighborhood G b ∩ A) ω.1)
  have hbudget : bitBudget (fun _ => m) t 0 r ≤ I.bits.length := by
    rw [constant_bitBudget]
    exact (Nat.le_add_right _ _).trans I.hbudget
  have hsub (a : List ℕ) : sourcePathFiber I ω a ⊆
      pathFiber (fun _ => m) t (fun _ => 0) 0 r
        I.bits.length indices a := by
    intro tape ht
    obtain ⟨w, hw⟩ := (Finset.mem_filter.mp ht).2
    have hindices := sourceOrderedDraw_indices_eq I ω
      w.values w.valuesLength w.orderedDraw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      simpa [indices, hindices, hw] using w.drawFlat⟩
  have hdisj : ∀ a ∈ attemptVectors t r,
      ∀ b ∈ attemptVectors t r,
      a ≠ b → Disjoint (sourcePathFiber I ω a)
        (sourcePathFiber I ω b) := by
    intro a _ b _ hab
    exact (pathFiber_disjoint (fun _ => m) t (fun _ => 0)
      0 r I.bits.length indices hab).mono (hsub a) (hsub b)
  have hsum : k * (sourceInitialOutcomeFiber I ω).card ≤
      (outputFiber (fun _ => m) t (fun _ => 0) 0 r
        I.bits.length indices).card := by
    rw [sourceInitialOutcomeFiber_eq_biUnion I ω,
      Finset.card_biUnion hdisj,
      outputFiber_eq_biUnion (fun _ => m) t (fun _ => 0)
        0 r I.bits.length indices hbudget,
      Finset.card_biUnion, Finset.mul_sum]
    · exact Finset.sum_le_sum fun a ha =>
        sourcePathFiber_le_firstPath I ω a ha
    · intro a ha b hb hab
      exact pathFiber_disjoint (fun _ => m) t (fun _ => 0)
        0 r I.bits.length indices hab
  have hfirst := outputFiber_le_ideal_uniform (fun _ => m) t
    (fun _ => 0) 0 r I.bits.length indices hbudget
    (indicesOfOutcome_valid I ω)
  rw [outputCount_const m 0 r] at hfirst
  calc
    m ^ r * k * (sourceInitialOutcomeFiber I ω).card =
        m ^ r * (k * (sourceInitialOutcomeFiber I ω).card) := by ring
    _ ≤ m ^ r * (outputFiber (fun _ => m) t (fun _ => 0)
        0 r I.bits.length indices).card := Nat.mul_le_mul_left _ hsum
    _ ≤ 2 ^ I.bits.length := hfirst

/-- Subprobability domination for one exact successful outcome of the
executed initial sampler on a uniform flat tape. -/
lemma sourceInitialOutcomeFiber_probability_le_outcomeWeight
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r) :
    ((sourceInitialOutcomeFiber I ω).card : ℚ) /
      (2 ^ I.bits.length : ℚ) ≤
    outcomeWeight A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r ω := by
  classical
  have hm : m = A.card := prefixEnumerates_card m I.domain A I.henum
  have hnat := sourceInitialOutcomeFiber_le_ideal I ω
  have hnat' : (sourceInitialOutcomeFiber I ω).card *
      (A.card ^ r * Fintype.card (RepChoices A
        (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) ω.1)) ≤
      2 ^ I.bits.length := by
    calc
      (sourceInitialOutcomeFiber I ω).card *
          (A.card ^ r * Fintype.card (RepChoices A
            (activeVertices n I.activeB)
            (fun b => numericNeighborhood G b ∩ A) ω.1)) =
          m ^ r * Fintype.card (RepChoices A
            (activeVertices n I.activeB)
            (fun b => numericNeighborhood G b ∩ A) ω.1) *
            (sourceInitialOutcomeFiber I ω).card := by
              conv => rhs; lhs; lhs; rw [hm]
              ring
      _ ≤ 2 ^ I.bits.length := hnat
  have hrepNonempty : Nonempty (RepChoices A
      (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) ω.1) :=
    ⟨fun T => Classical.choice (repFiberNonempty A
      (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) ω.1 T)⟩
  have hrepPos : 0 < Fintype.card (RepChoices A
      (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) ω.1) :=
    Fintype.card_pos_iff.mpr hrepNonempty
  have hden : 0 < (A.card ^ r : ℚ) *
      (Fintype.card (RepChoices A
        (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) ω.1) : ℚ) := by
    have hA : 0 < A.card := by simpa [← hm] using I.hmPos
    positivity
  have hpow : 0 < (2 ^ I.bits.length : ℚ) := by positivity
  unfold outcomeWeight
  apply (div_le_div_iff₀ hpow hden).mpr
  have hnatQ : ((sourceInitialOutcomeFiber I ω).card : ℚ) *
      ((A.card ^ r : ℚ) *
        (Fintype.card (RepChoices A
          (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) ω.1) : ℚ)) ≤
      (2 ^ I.bits.length : ℚ) := by exact_mod_cast hnat'
  simpa [mul_assoc] using hnatQ

/-- Completed actual initial attempts whose decoded exception predicate
rejects. A failed capped selector has no successful outcome witness and is
outside this retry-continuation event. -/
noncomputable def sourceInitialBadFiber
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (threshold cap : ℕ) : Finset (FlatTape I.bits.length) := by
  classical
  exact ((Finset.univ : Finset (InitialOutcome A
      (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r)).filter fun ω =>
        outcomeBad A (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) r threshold cap ω = true
      ).biUnion (sourceInitialOutcomeFiber I)

/-- If the full attempt's acceptance scan rejects after successful
selection, its exact bit tape lies in the actual continuation fiber. -/
lemma initialSamplerAttempt_run_badFiber
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (σsel : Env) (K threshold cap : ℕ)
    (choice : InitialChoice A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r)
    (mapped : ℕ → ℕ)
    (hsel : Run B initialSamplerAttempt I.σ σsel K)
    (hbatch : σsel.vars "batchFailed" = 0)
    (hrep : σsel.vars "repFailed" = 0)
    (harray : σsel.arrs "repB" = arrOf n mapped)
    (hchoice : ∀ b ∈ activeVertices n I.activeB,
      choice.representative b = mapped b)
    (hbad : cap < (choice.exceptions threshold).card) :
    (flatBitsEquiv I.bits.length).symm ⟨I.bits, rfl⟩ ∈
      sourceInitialBadFiber I threshold cap := by
  classical
  obtain ⟨σsource, Ksource, hsourceRun, houtcome⟩ :=
    initialSamplerAttempt_run_sourceOutcome I
  have hfinal : σsource = σsel := by
    obtain ⟨_, _, hbig⟩ := hsourceRun
    obtain ⟨_, _, hbig'⟩ := hsel
    exact (BigStep.unique hbig.bigStep hbig'.bigStep).1
  obtain ⟨ω, hω⟩ := houtcome (by simpa [hfinal] using hbatch)
    (by simpa [hfinal] using hrep)
  have hbits : flatBits ((flatBitsEquiv I.bits.length).symm
      ⟨I.bits, rfl⟩) = I.bits :=
    congrArg Subtype.val
      ((flatBitsEquiv I.bits.length).apply_symm_apply ⟨I.bits, rfl⟩)
  obtain ⟨w⟩ := (Finset.mem_filter.mp hω).2
  have hinputState :
      {I.σ with inp := I.bits.map Bool.toNat ++ I.rest} = I.σ := by
    simp [← I.hinput]
  have hfinalW : w.σfinal = σsel := by
    have hwRunRaw : Run B initialSamplerAttempt
        {I.σ with inp := I.bits.map Bool.toNat ++ I.rest}
        w.σfinal w.attemptCost := by
      simpa only [hbits] using w.attemptRun
    have hwRun : Run B initialSamplerAttempt I.σ w.σfinal
        w.attemptCost := by simpa only [hinputState] using hwRunRaw
    obtain ⟨_, _, hbig⟩ := hwRun
    obtain ⟨_, _, hbig'⟩ := hsel
    exact (BigStep.unique hbig.bigStep hbig'.bigStep).1
  have hmapped : ∀ b ∈ activeVertices n I.activeB,
      w.mapped b = mapped b := by
    intro b hb
    have hbn : b < n := (mem_activeVertices.mp hb).1
    have harr : arrOf n w.mapped = arrOf n mapped := by
      calc
        arrOf n w.mapped = w.σfinal.arrs "repB" := w.resultArray.symm
        _ = σsel.arrs "repB" := by rw [hfinalW]
        _ = arrOf n mapped := harray
    exact arrOf_eq_on harr b hbn
  have hexceptions :
      (outcomeChoice A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r ω).exceptions threshold =
      choice.exceptions threshold := by
    ext b
    simp only [InitialChoice.exceptions, Finset.mem_filter]
    constructor
    · rintro ⟨hb, hd⟩
      refine ⟨hb, ?_⟩
      rw [w.representative b hb, hmapped b hb,
        ← hchoice b hb] at hd
      exact hd
    · rintro ⟨hb, hd⟩
      refine ⟨hb, ?_⟩
      rw [w.representative b hb, hmapped b hb,
        ← hchoice b hb]
      exact hd
  have hbadω : outcomeBad A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r threshold cap ω = true := by
    simp [outcomeBad, hexceptions, hbad]
  apply Finset.mem_biUnion.mpr
  refine ⟨ω, ?_, hω⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbadω⟩

/-- The source witness inside a rejecting fiber consumed exactly the prefix
reported by the checked selection Run. This identifies the split point for
the following retry, including all rejected selector blocks. -/
lemma sourceInitialBadFiber_consumed
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (σsel : Env) (K d threshold cap : ℕ)
    (hsel : Run B initialSamplerAttempt I.σ σsel K)
    (hinp : σsel.inp = (I.bits.drop d).map Bool.toNat ++ I.rest)
    (hd : d ≤ I.bits.length)
    (hbad : (flatBitsEquiv I.bits.length).symm ⟨I.bits, rfl⟩ ∈
      sourceInitialBadFiber I threshold cap) :
    ∃ ω : InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r,
      outcomeBad A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r threshold cap ω = true ∧
      ∃ w : SourceInitialOutcomeWitness I I.bits ω,
        d = w.used * Nat.clog 2 m + w.repUsed := by
  classical
  obtain ⟨ω, hωbad, hω⟩ := Finset.mem_biUnion.mp hbad
  have hbadω := (Finset.mem_filter.mp hωbad).2
  have hbits : flatBits ((flatBitsEquiv I.bits.length).symm
      ⟨I.bits, rfl⟩) = I.bits :=
    congrArg Subtype.val
      ((flatBitsEquiv I.bits.length).apply_symm_apply ⟨I.bits, rfl⟩)
  have hw : Nonempty (SourceInitialOutcomeWitness I I.bits ω) := by
    simpa only [sourceInitialOutcomeFiber, Finset.mem_filter,
      Finset.mem_univ, true_and, hbits] using hω
  obtain ⟨w⟩ := hw
  have hstate : {I.σ with inp := I.bits.map Bool.toNat ++ I.rest} = I.σ := by
    simp [← I.hinput]
  have hwRun : Run B initialSamplerAttempt I.σ w.σfinal
      w.attemptCost := by simpa only [hstate] using w.attemptRun
  have hfinal : w.σfinal = σsel := by
    obtain ⟨_, _, hbig⟩ := hwRun
    obtain ⟨_, _, hbig'⟩ := hsel
    exact (BigStep.unique hbig.bigStep hbig'.bigStep).1
  have hdropLen :
      (I.bits.drop (w.used * Nat.clog 2 m + w.repUsed)).length =
      (I.bits.drop d).length := by
    have heq :
        (I.bits.drop (w.used * Nat.clog 2 m + w.repUsed)).map Bool.toNat ++
            I.rest = (I.bits.drop d).map Bool.toNat ++ I.rest := by
      rw [← w.attemptInput, hfinal]
      exact hinp
    have hmap := List.append_cancel_right heq
    simpa only [List.length_map] using congrArg List.length hmap
  have hdrawBudget : bitBudget (fun _ => m) t 0 r ≤ I.bits.length := by
    rw [constant_bitBudget]
    exact (Nat.le_add_right _ _).trans I.hbudget
  have hdrawLe : w.used * Nat.clog 2 m ≤ I.bits.length := by
    rw [← w.consumed]
    exact (ValidPath.consumedBits_le_budget (fun _ => m) t
      (fun _ => 0) (FlatClassSuccess.validPath (fun _ => m) t
        (fun _ => 0) w.drawFlat)).trans hdrawBudget
  have hrepLe : w.repUsed ≤
      (I.bits.drop (w.used * Nat.clog 2 m)).length :=
    ClassTrace.used_le w.size t (classStart w.size) w.classTrace
  have htotal : w.used * Nat.clog 2 m + w.repUsed ≤
      I.bits.length := by
    simp only [List.length_drop] at hrepLe
    omega
  have heq : d = w.used * Nat.clog 2 m + w.repUsed := by
    simp only [List.length_drop] at hdropLen
    omega
  exact ⟨ω, hbadω, w, heq⟩

lemma sourceInitialBadFiber_probability_le_badMass
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (threshold cap : ℕ) :
    ((sourceInitialBadFiber I threshold cap).card : ℚ) /
      (2 ^ I.bits.length : ℚ) ≤
    badMass
      (outcomeWeight A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r)
      (outcomeBad A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r threshold cap) := by
  classical
  let bad : Finset (InitialOutcome A (activeVertices n I.activeB)
      (fun b => numericNeighborhood G b ∩ A) r) :=
    Finset.univ.filter fun ω =>
      outcomeBad A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r threshold cap ω = true
  have hcard : (sourceInitialBadFiber I threshold cap).card ≤
      ∑ ω ∈ bad, (sourceInitialOutcomeFiber I ω).card := by
    exact Finset.card_biUnion_le
  have hcardQ : ((sourceInitialBadFiber I threshold cap).card : ℚ) ≤
      ∑ ω ∈ bad, ((sourceInitialOutcomeFiber I ω).card : ℚ) := by
    exact_mod_cast hcard
  have hden : 0 < (2 ^ I.bits.length : ℚ) := by positivity
  calc
    ((sourceInitialBadFiber I threshold cap).card : ℚ) /
        (2 ^ I.bits.length : ℚ) ≤
      (∑ ω ∈ bad, ((sourceInitialOutcomeFiber I ω).card : ℚ)) /
        (2 ^ I.bits.length : ℚ) :=
          (div_le_div_iff₀ hden hden).mpr (by nlinarith [hcardQ])
    _ = ∑ ω ∈ bad,
        ((sourceInitialOutcomeFiber I ω).card : ℚ) /
          (2 ^ I.bits.length : ℚ) := by simp [Finset.sum_div]
    _ ≤ ∑ ω ∈ bad,
        outcomeWeight A (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) r ω := by
            apply Finset.sum_le_sum
            intro ω _
            exact sourceInitialOutcomeFiber_probability_le_outcomeWeight I ω
    _ = badMass
        (outcomeWeight A (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) r)
        (outcomeBad A (activeVertices n I.activeB)
          (fun b => numericNeighborhood G b ∩ A) r threshold cap) := by
            simp [badMass, bad, Finset.sum_filter]

/-- The actual retry-continuation event inherits any half-mass bound on
mathematical rejection; selector exhaustion contributes zero continuation
mass. -/
lemma sourceInitialBadFiber_half
    {B n m domainCap r t bufferCap targetCap Q : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ} {A : Finset ℕ}
    (I : Lax457868Proofs.InitialSamplerAttempt.Input
      B n m domainCap r t bufferCap targetCap Q G x A)
    (threshold cap : ℕ)
    (hmass : badMass
      (outcomeWeight A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r)
      (outcomeBad A (activeVertices n I.activeB)
        (fun b => numericNeighborhood G b ∩ A) r threshold cap) ≤
          (1 / 2 : ℚ)) :
    2 * (sourceInitialBadFiber I threshold cap).card ≤
      2 ^ I.bits.length := by
  have hprob := (sourceInitialBadFiber_probability_le_badMass
    I threshold cap).trans hmass
  have hden : 0 < (2 ^ I.bits.length : ℚ) := by positivity
  have hq : (2 : ℚ) *
      ((sourceInitialBadFiber I threshold cap).card : ℚ) ≤
      (2 ^ I.bits.length : ℚ) := by
    have h := (div_le_iff₀ hden).mp hprob
    nlinarith
  exact_mod_cast hq

/-- Occupied classes always admit a numeric output vector, including when
the capped selector later aborts before producing one. -/
lemma exists_validOutput_of_positive (size start : ℕ → ℕ)
    (d q : ℕ) (hpos : ∀ j < q, 0 < size (d + j)) :
    ∃ values, ValidOutput size start d q values := by
  induction q generalizing d with
  | zero => exact ⟨[], ValidOutput.done d⟩
  | succ q ih =>
      have hd : 0 < size d := by simpa using hpos 0 (by omega)
      obtain ⟨tail, htail⟩ := ih (d + 1) (by
        intro j hj
        have h := hpos (j + 1) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h)
      exact ⟨start d :: tail,
        ValidOutput.step ⟨0, hd⟩ htail⟩

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
