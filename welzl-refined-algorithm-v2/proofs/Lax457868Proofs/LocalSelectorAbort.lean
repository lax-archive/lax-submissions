import Lax457868Proofs.InitialAbortProbability
import Lax457868Proofs.ExceptionRepairMean

/-! Flat selector failure in the actual local retry loop. -/
namespace Lax457868Proofs.LocalSelectorAbort

open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.StoppingPrefix
open Lax457868Proofs.InitialAbortProbability
open Lax457868Proofs.LocalRepairRetriesSource

/-- The rejection predicate only reads occupied domain cells. In particular,
uninitialized cells past the selector modulus cannot affect either failure
count. -/
lemma localBadOutputs_congr_domain (m s : ℕ) (d₁ d₂ : ℕ → ℕ)
    (N : ℕ → Finset ℕ) (B W : Finset ℕ) (b : ℕ)
    (h : ∀ j, j < m → d₁ j = d₂ j) :
    LocalFlatLaw.localBadOutputs m s d₁ N B W b =
      LocalFlatLaw.localBadOutputs m s d₂ N B W b := by
  classical
  ext output
  simp only [LocalFlatLaw.localBadOutputs, Finset.mem_filter]
  constructor
  · rintro ⟨hvalid, hbad⟩
    refine ⟨hvalid, ?_⟩
    obtain ⟨indices, _, houtput⟩ := Finset.mem_image.mp
      ((LocalFlatLaw.outputVectors_eq_indexOutput_image m 0 s) ▸ hvalid)
    subst output
    have heq : (LocalFlatLaw.indexOutput indices).map d₁ =
        (LocalFlatLaw.indexOutput indices).map d₂ := by
      simp only [LocalFlatLaw.indexOutput, List.map_ofFn]
      congr 1
      funext i
      exact h _ (indices i).isLt
    rwa [← heq]
  · rintro ⟨hvalid, hbad⟩
    refine ⟨hvalid, ?_⟩
    obtain ⟨indices, _, houtput⟩ := Finset.mem_image.mp
      ((LocalFlatLaw.outputVectors_eq_indexOutput_image m 0 s) ▸ hvalid)
    subst output
    have heq : (LocalFlatLaw.indexOutput indices).map d₁ =
        (LocalFlatLaw.indexOutput indices).map d₂ := by
      simp only [LocalFlatLaw.indexOutput, List.map_ofFn]
      congr 1
      funext i
      exact h _ (indices i).isLt
    rwa [heq]

/-- A successful constant-width selector trace can be followed by a failed
trace on precisely its unread suffix. -/
lemma classTrace_splice_failed (m t : ℕ) :
    ∀ {d r q : ℕ} {bits : List Bool} {values : List ℕ}
      {used charge : ℕ} {failed : Bool},
      ClassTrace (fun _ => m) t (fun _ => 0) d r bits values used charge failed →
      failed = false →
      (∃ values' used' charge',
        ClassTrace (fun _ => m) t (fun _ => 0) (d + r) q
          (bits.drop used) values' used' charge' true) →
      ∃ values' used' charge',
        ClassTrace (fun _ => m) t (fun _ => 0) d (r + q)
          bits values' used' charge' true := by
  intro d r q bits values used charge failed h
  induction h generalizing q with
  | done d bits =>
      intro _ hnext
      simpa using hnext
  | failed tape tail u hm hsel =>
      intro hf _
      contradiction
  | @accepted d r tape tail i u values used charge failed hm hsel htail ih =>
      intro hf hnext
      have hu : u ≤ t :=
        (stoppedEvent_bounds m hm t u i tape hsel).2
      have hdrop : (tapeBits tape ++ tail).drop (u * Nat.clog 2 m) =
          (tapeBits tape).drop (u * Nat.clog 2 m) ++ tail := by
        rw [List.drop_append]
        have hle : u * Nat.clog 2 m ≤ (tapeBits tape).length := by
          simpa [tapeBits_length] using Nat.mul_le_mul_right (Nat.clog 2 m) hu
        simp [hle]
      have hdrop2 : (tapeBits tape ++ tail).drop
          (u * Nat.clog 2 m + used) =
          (((tapeBits tape).drop (u * Nat.clog 2 m) ++ tail).drop used) := by
        rw [← List.drop_drop, hdrop]
      have hnext' : ∃ values' used' charge',
          ClassTrace (fun _ => m) t (fun _ => 0) (d + 1 + r) q
            (((tapeBits tape).drop (u * Nat.clog 2 m) ++ tail).drop used)
            values' used' charge' true := by
        simpa [Nat.add_assoc, Nat.add_comm r 1,
          Nat.add_comm used (u * Nat.clog 2 m), hdrop2] using hnext
      obtain ⟨v, u', c, htailFailed⟩ := ih hf hnext'
      refine ⟨(0 + i.val) :: v, u * Nat.clog 2 m + u',
        (15 * Nat.clog 2 m + 30) * u + 12 * Nat.clog 2 m + 61 + c, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ClassTrace.accepted (size := fun _ => m) (t := t)
          (start := fun _ => 0) (d := d) (r := r + q)
          tape tail i u hm hsel htailFailed)

/-- A terminal failed capped selector after complete rejected trials is a
failed constant-width class trace of all selectors attempted so far. -/
lemma flatSelectorFailed_to_classTrace (m t s : ℕ) (hm : 0 < m)
    (bad : Finset (List ℕ)) :
    ∀ {attempts : ℕ} {bits : List Bool},
      FlatSelectorFailed m hm t s bad attempts bits →
      ∀ d, ∃ values used charge,
        ClassTrace (fun _ => m) t (fun _ => 0) d
          (attempts * s) bits values used charge true := by
  intro attempts bits hfailed
  induction hfailed with
  | final blockTape tail values used hbits hdraw =>
      intro d
      obtain ⟨charge, hclass⟩ :=
        Lax457868Proofs.InitialFlatLaw.drawTrace_to_classTrace
          m hm t d hdraw
      have hclass' := Lax457868Proofs.InitialAbortProbability.ClassTrace.append_bits hclass tail
      refine ⟨values.map Fin.val, used * Nat.clog 2 m, charge, ?_⟩
      simpa [hbits, tapeBits, Nat.one_mul] using hclass'
  | @rejected bits k blockTape tail values used hbits hdraw hbad hnext ih =>
      intro d
      obtain ⟨charge, hclass⟩ :=
        Lax457868Proofs.InitialFlatLaw.drawTrace_to_classTrace
          m hm t d hdraw
      have hprefix : ClassTrace (fun _ => m) t (fun _ => 0) d s
          bits (values.map Fin.val) (used * Nat.clog 2 m) charge false := by
        have hh := Lax457868Proofs.InitialAbortProbability.ClassTrace.append_bits hclass tail
        simpa [hbits, tapeBits] using hh
      obtain ⟨v, u, c, htail⟩ := ih (d + s)
      obtain ⟨v', u', c', hwhole⟩ :=
        classTrace_splice_failed m t hprefix rfl ⟨v, u, c, htail⟩
      refine ⟨v', u', c', ?_⟩
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_assoc] using hwhole


/-- Once a selector has failed, increasing the unattempted request count
preserves the same failed trace and stopped prefix. -/
lemma classTrace_extend_failed (m t : ℕ) :
    ∀ {d r : ℕ} {bits : List Bool} {values : List ℕ}
      {used charge : ℕ} {failed : Bool},
      ClassTrace (fun _ => m) t (fun _ => 0) d r bits values used charge failed →
      failed = true → ∀ extra, ∃ values' used' charge',
        ClassTrace (fun _ => m) t (fun _ => 0) d (r + extra)
          bits values' used' charge' true := by
  intro d r bits values used charge failed h
  induction h with
  | done d bits =>
      intro hf
      contradiction
  | @failed d r tape tail u hm hsel =>
      intro _ extra
      refine ⟨[], u * Nat.clog 2 m,
        (15 * Nat.clog 2 m + 30) * u + 12 * Nat.clog 2 m + 61, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ClassTrace.failed (size := fun _ => m) (t := t)
          (start := fun _ => 0) (d := d) (r := r + extra)
          tape tail u hm hsel)
  | @accepted d r tape tail i u values used charge failed hm hsel hnext ih =>
      intro hf extra
      obtain ⟨v, u', c, htail⟩ := ih hf extra
      refine ⟨i.val :: v, u * Nat.clog 2 m + u',
        (15 * Nat.clog 2 m + 30) * u + 12 * Nat.clog 2 m + 61 + c, ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        (ClassTrace.accepted (size := fun _ => m) (t := t)
          (start := fun _ => 0) (d := d) (r := r + extra)
          tape tail i u hm hsel htail)

/-- Every actual local status-two event is included in failure of a single
flat class-selector trace with `cap*s` potential calls. The generic count
therefore pays only for actually reachable adaptive selector positions. -/
lemma selector_failure_count_le (m t s cap Nbits : ℕ)
    (bad : Finset (List ℕ)) (hm : 0 < m)
    (hbudget : cap * s * t * Nat.clog 2 m ≤ Nbits)
    (failed : FlatTraceLaw.FlatTape Nbits → Prop) [DecidablePred failed]
    (htrace : ∀ tape, failed tape →
      ∃ attempts, attempts ≤ cap ∧
        FlatSelectorFailed m hm t s bad
          attempts (FlatTraceLaw.flatBits tape)) :
    2 ^ t * (Finset.univ.filter failed).card ≤
      cap * s * 2 ^ Nbits := by
  classical
  have hsub : (Finset.univ.filter failed) ⊆
      Finset.univ.filter (fun tape : FlatTraceLaw.FlatTape Nbits =>
        failedFlag (fun _ => m) t (fun _ => 0) 0 (cap * s)
          (FlatTraceLaw.flatBits tape) = true) := by
    intro tape htape
    obtain ⟨attempts, ha, hfailed⟩ :=
      htrace tape (Finset.mem_filter.mp htape).2
    obtain ⟨v, u, c, hclass⟩ :=
      flatSelectorFailed_to_classTrace m t s hm bad hfailed 0
    let extra := (cap - attempts) * s
    obtain ⟨v', u', c', hclass'⟩ :=
      classTrace_extend_failed m t hclass rfl extra
    have hcount : attempts * s + extra = cap * s := by
      dsimp [extra]
      calc
        attempts * s + (cap - attempts) * s =
            (attempts + (cap - attempts)) * s := by ring
        _ = cap * s := by rw [Nat.add_sub_of_le ha]
    have hh : failedFlag (fun _ => m) t (fun _ => 0) 0 (cap * s)
        (FlatTraceLaw.flatBits tape) = true := by
      rw [← hcount]
      exact failedFlag_eq hclass'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩
  have hbudget' : ClassRepresentativeTrace.bitBudget
      (fun _ => m) t 0 (cap * s) ≤ Nbits := by
    rw [constant_bitBudget]
    simpa [Nat.mul_assoc] using hbudget
  have hcount := class_failure_count_bound
    (fun _ => m) t (fun _ => 0) (cap * s) 0 Nbits
    (fun _ _ _ => hm) hbudget'
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans hcount


end Lax457868Proofs.LocalSelectorAbort
