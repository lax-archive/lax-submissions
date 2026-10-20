import Mathlib.Tactic
import Lax457868Proofs.FlatTraceLaw
import Lax457868Proofs.LocalRepairSource
import Lax457868Proofs.SamplerLocalSuccess
import Lax457868Proofs.SamplerRetries
import Lax457868Proofs.EnumeratedDraws

/-!
The actual local selector may abort when one of its capped index draws fails.
The event counted here contains only completed draw traces whose local scan
rejects and therefore continues the retry loop. Each accepted index consumes
only its stopped prefix; the rest of the flat tape remains available.
-/

namespace Lax457868Proofs.LocalFlatLaw

open FlatTraceLaw ClassRepresentativeTrace SequentialDraws

noncomputable section

/-- The trial reserves `s` capped calls of width `clog2 m`; its trace
consumes only the successful stopped prefixes within that bound. -/
lemma local_bitBudget (m t s : ℕ) :
    bitBudget (fun _ => m) t 0 s = s * t * Nat.clog 2 m := by
  have h (d : ℕ) : ∀ r : ℕ,
      bitBudget (fun _ => m) t d r = r * t * Nat.clog 2 m := by
    intro r
    induction r generalizing d with
    | zero => simp [bitBudget]
    | succ r ih =>
        simp only [bitBudget]
        rw [ih (d + 1)]
        ring
  exact h 0 s

/-- Ordered ideal index outputs, in the same list format as the source
`DrawTrace`. -/
def indexOutput {m s : ℕ} (tape : Fin s → Fin m) : List ℕ :=
  List.ofFn fun i => (tape i).val

lemma indexOutput_injective (m s : ℕ) :
    Function.Injective (indexOutput (m := m) (s := s)) := by
  intro a b hab
  have hvalues : (fun i : Fin s => (a i).val) =
      (fun i : Fin s => (b i).val) := List.ofFn_inj.mp hab
  funext i
  exact Fin.ext (congrFun hvalues i)

lemma indexOutput_valid (m : ℕ) :
    ∀ (d s : ℕ) (tape : Fin s → Fin m),
      ValidOutput (fun _ => m) (fun _ => 0) d s (indexOutput tape)
  | d, 0, tape => by
      simpa [indexOutput] using
        (ValidOutput.done (size := fun _ => m) (start := fun _ => 0) d)
  | d, s + 1, tape => by
      have hnext := indexOutput_valid m (d + 1) s (fun i => tape i.succ)
      have hstep := ValidOutput.step (d := d) (r := s) (tape 0) hnext
      simpa [indexOutput, List.ofFn_succ] using hstep

lemma validOutput_exists_indexOutput (m : ℕ) :
    ∀ {d s : ℕ} {output : List ℕ},
      ValidOutput (fun _ => m) (fun _ => 0) d s output →
        ∃ tape : Fin s → Fin m, indexOutput tape = output
  | _, _, _, .done _ => ⟨Fin.elim0, by simp [indexOutput]⟩
  | _, _, _, .step i hnext => by
      obtain ⟨tail, htail⟩ := validOutput_exists_indexOutput m hnext
      refine ⟨Fin.cons i tail, ?_⟩
      simpa [indexOutput, List.ofFn_succ, htail]

lemma outputVectors_eq_indexOutput_image (m d s : ℕ) :
    outputVectors (fun _ => m) (fun _ => 0) d s =
      (Finset.univ : Finset (Fin s → Fin m)).image indexOutput := by
  classical
  ext output
  constructor
  · intro houtput
    obtain ⟨tape, htape⟩ := validOutput_exists_indexOutput m
      (outputVectors.validOutput (fun _ => m) (fun _ => 0) houtput)
    exact Finset.mem_image.mpr ⟨tape, Finset.mem_univ _, htape⟩
  · intro houtput
    obtain ⟨tape, _, rfl⟩ := Finset.mem_image.mp houtput
    exact ValidOutput.mem_outputVectors (fun _ => m) (fun _ => 0)
      (indexOutput_valid m d s tape)

/-- Rejected ideal index tapes before decoding through the occupied
source domain array. -/
def localBadIndexTapes (m s : ℕ) (domain : ℕ → ℕ)
    (N : ℕ → Finset ℕ) (B : Finset ℕ) (W : Finset ℕ) (b : ℕ) :
    Finset (Fin s → Fin m) := by
  classical
  exact Finset.univ.filter fun tape =>
    ¬ SamplerPhases.localTrialIsolates N B W b
      ((indexOutput tape).map domain)

/-- The source domain enumeration gives a bijection between ideal index
tapes and uniform ordered tapes of elements of `X`. -/
noncomputable def indexTapeEquiv (m s : ℕ) (domain : ℕ → ℕ)
    (X : Finset ℕ)
    (henum : ReusedOriginal.Construction.MarkingMath.PrefixEnumerates m domain X) :
    (Fin s → Fin m) ≃ SamplerUniformDraws.Tape X s where
  toFun tape i := EnumeratedDraws.prefixIndexEquiv m domain X henum (tape i)
  invFun tape i := (EnumeratedDraws.prefixIndexEquiv m domain X henum).symm (tape i)
  left_inv tape := by
    funext i
    exact (EnumeratedDraws.prefixIndexEquiv m domain X henum).symm_apply_apply (tape i)
  right_inv tape := by
    funext i
    exact (EnumeratedDraws.prefixIndexEquiv m domain X henum).apply_symm_apply (tape i)

lemma indexTapeEquiv_toList (m s : ℕ) (domain : ℕ → ℕ)
    (X : Finset ℕ)
    (henum : ReusedOriginal.Construction.MarkingMath.PrefixEnumerates m domain X)
    (tape : Fin s → Fin m) :
    (indexTapeEquiv m s domain X henum tape).toList =
      (indexOutput tape).map domain := by
  simp [SamplerUniformDraws.Tape.toList, indexTapeEquiv, indexOutput,
    List.map_ofFn, EnumeratedDraws.prefixIndexEquiv]
  funext i
  rfl

/-- A successful actual block trace with prescribed indices on one flat tape.
The equality retains the exact block order and every unread bit. -/
def actualDrawOutputFiber (m : ℕ) (hm : 0 < m) (t s N : ℕ)
    (output : List ℕ) : Finset (FlatTape N) := by
  classical
  exact Finset.univ.filter fun tape =>
    ∃ (blocks : List (Fin (Nat.clog 2 m) → Bool))
      (values : List (Fin m)) (used : ℕ),
      blocks.flatMap List.ofFn = flatBits tape ∧
      DrawTrace m hm t s blocks values used false ∧
      values.map Fin.val = output

/-- A completed source draw is one of the successful fixed-output fibers of
`FlatTraceLaw`; no selector-failure trace can satisfy this membership. -/
lemma actualDrawOutputFiber_subset_outputFiber (m : ℕ) (hm : 0 < m)
    (t s N : ℕ) (output : List ℕ)
    (hbudget : bitBudget (fun _ => m) t 0 s ≤ N) :
    actualDrawOutputFiber m hm t s N output ⊆
      outputFiber (fun _ => m) t (fun _ => 0) 0 s N output := by
  intro tape htape
  obtain ⟨blocks, values, used, hbits, htrace, houtput⟩ := by
    simpa only [actualDrawOutputFiber, Finset.mem_filter,
      Finset.mem_univ, true_and] using htape
  obtain ⟨attempts, hflat⟩ :=
    drawTrace_success_to_flat m hm t 0 htrace rfl
  rw [hbits, houtput] at hflat
  obtain ⟨used', charge, hclass, _, _⟩ :=
    flatClassSuccess_to_classTrace (fun _ => m) t (fun _ => 0)
      hflat (by simpa using hbudget)
  change tape ∈ outputFiber (fun _ => m) t (fun _ => 0) 0 s N output
  simp only [outputFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨used', charge, hclass⟩

/-- Completed actual traces whose output lies in a prescribed rejecting set.
Selector failures are absent because the trace's final flag must be false. -/
def actualRejectedFiber (m : ℕ) (hm : 0 < m) (t s N : ℕ)
    (bad : Finset (List ℕ)) : Finset (FlatTape N) :=
  bad.biUnion (actualDrawOutputFiber m hm t s N)

/-- The ideal class trace's rejecting event on the same complete bit tape. -/
def classRejectedFiber (m t s N : ℕ)
    (bad : Finset (List ℕ)) : Finset (FlatTape N) :=
  bad.biUnion (outputFiber (fun _ => m) t (fun _ => 0) 0 s N)

lemma actualRejectedFiber_subset_classRejectedFiber (m : ℕ)
    (hm : 0 < m) (t s N : ℕ) (bad : Finset (List ℕ))
    (hbudget : bitBudget (fun _ => m) t 0 s ≤ N) :
    actualRejectedFiber m hm t s N bad ⊆ classRejectedFiber m t s N bad := by
  intro tape htape
  obtain ⟨output, hbad, hmem⟩ := Finset.mem_biUnion.mp htape
  exact Finset.mem_biUnion.mpr
    ⟨output, hbad,
      actualDrawOutputFiber_subset_outputFiber m hm t s N output hbudget hmem⟩

/-- A rejecting set occupying at most half the ideal Cartesian outputs
occupies at most half of all flat fair-bit tapes even for the actual capped
selector. The missing selector-success mass is never normalized away. -/
lemma actualRejectedFiber_half (m : ℕ) (hm : 0 < m)
    (t s N : ℕ) (bad : Finset (List ℕ))
    (hbudget : bitBudget (fun _ => m) t 0 s ≤ N)
    (hvalid : bad ⊆ outputVectors (fun _ => m) (fun _ => 0) 0 s)
    (hhalf : 2 * bad.card ≤ outputCount (fun _ => m) 0 s) :
    2 * (actualRejectedFiber m hm t s N bad).card ≤ 2 ^ N := by
  let weight := jointWeight (fun _ => m) t 0 s N
  have hsmall : (actualRejectedFiber m hm t s N bad).card ≤
      bad.card * weight := by
    calc
      (actualRejectedFiber m hm t s N bad).card ≤
          (classRejectedFiber m t s N bad).card :=
        Finset.card_le_card
          (actualRejectedFiber_subset_classRejectedFiber m hm t s N bad hbudget)
      _ ≤ ∑ output ∈ bad,
          (outputFiber (fun _ => m) t (fun _ => 0) 0 s N output).card := by
        exact Finset.card_biUnion_le
      _ = bad.card * weight := by
        have hcard : ∀ output ∈ bad,
            (outputFiber (fun _ => m) t (fun _ => 0) 0 s N output).card =
              weight := by
          intro output houtput
          exact card_outputFiber_valid (fun _ => m) t (fun _ => 0) 0 s N
            output hbudget
            (outputVectors.validOutput (fun _ => m) (fun _ => 0)
              (hvalid houtput))
        simp_rw [Finset.sum_congr rfl hcard]
        simp [weight]
  have htotal : outputCount (fun _ => m) 0 s * weight ≤ 2 ^ N := by
    rw [← card_successFiber (fun _ => m) t (fun _ => 0) 0 s N hbudget]
    simpa [FlatTape] using
      (Finset.card_le_card
        (Finset.subset_univ
          (successFiber (fun _ => m) t (fun _ => 0) 0 s N)))
  calc
    2 * (actualRejectedFiber m hm t s N bad).card ≤
        2 * (bad.card * weight) := Nat.mul_le_mul_left 2 hsmall
    _ = (2 * bad.card) * weight := by ring
    _ ≤ outputCount (fun _ => m) 0 s * weight :=
      Nat.mul_le_mul_right weight hhalf
    _ ≤ 2 ^ N := htotal

/-- Numeric index lists rejected by the actual local isolation predicate.
Only legal complete output vectors are included. -/
def localBadOutputs (m s : ℕ) (domain : ℕ → ℕ)
    (N : ℕ → Finset ℕ) (B : Finset ℕ) (W : Finset ℕ) (b : ℕ) :
    Finset (List ℕ) := by
  classical
  exact (outputVectors (fun _ => m) (fun _ => 0) 0 s).filter fun output =>
    ¬ SamplerPhases.localTrialIsolates N B W b (output.map domain)

lemma localBadOutputs_eq_indexImage (m s : ℕ) (domain : ℕ → ℕ)
    (N : ℕ → Finset ℕ) (B : Finset ℕ) (W : Finset ℕ) (b : ℕ) :
    localBadOutputs m s domain N B W b =
      (localBadIndexTapes m s domain N B W b).image indexOutput := by
  classical
  ext output
  simp only [localBadOutputs, localBadIndexTapes,
    outputVectors_eq_indexOutput_image, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨tape, houtput⟩, hbad⟩
    subst output
    exact ⟨tape, hbad, rfl⟩
  · rintro ⟨tape, hbad, houtput⟩
    subst output
    exact ⟨⟨tape, rfl⟩, hbad⟩

lemma card_localBadOutputs_eq_indexBad (m s : ℕ) (domain : ℕ → ℕ)
    (N : ℕ → Finset ℕ) (B : Finset ℕ) (W : Finset ℕ) (b : ℕ) :
    (localBadOutputs m s domain N B W b).card =
      (localBadIndexTapes m s domain N B W b).card := by
  rw [localBadOutputs_eq_indexImage]
  exact Finset.card_image_of_injective _ (indexOutput_injective m s)

lemma localBadIndexTapes_image_eq_failureSet
    (m s : ℕ) (domain : ℕ → ℕ) (X : Finset ℕ)
    (henum : ReusedOriginal.Construction.MarkingMath.PrefixEnumerates m domain X)
    (N : ℕ → Finset ℕ) (B : Finset ℕ) (W : Finset ℕ) (b : ℕ) :
    (localBadIndexTapes m s domain N B W b).image
      (indexTapeEquiv m s domain X henum) =
        SamplerLocalSuccess.localTrialFailureSet N B W b X s := by
  classical
  ext tape
  constructor
  · intro hmem
    obtain ⟨indices, hbad, rfl⟩ := Finset.mem_image.mp hmem
    have hreject : ¬ SamplerPhases.localTrialIsolates N B W b
        ((indexOutput indices).map domain) := by
      simpa [localBadIndexTapes] using hbad
    change (indexTapeEquiv m s domain X henum indices) ∈
      SamplerLocalSuccess.localTrialFailureSet N B W b X s
    simp only [SamplerLocalSuccess.localTrialFailureSet,
      Finset.mem_filter, Finset.mem_univ, true_and]
    rw [indexTapeEquiv_toList]
    exact hreject
  · intro hmem
    let indices := (indexTapeEquiv m s domain X henum).symm tape
    have hreject : ¬ SamplerPhases.localTrialIsolates N B W b tape.toList := by
      simpa [SamplerLocalSuccess.localTrialFailureSet] using hmem
    apply Finset.mem_image.mpr
    refine ⟨indices, ?_, ?_⟩
    · have hrejectIndices : ¬ SamplerPhases.localTrialIsolates N B W b
          ((indexOutput indices).map domain) := by
        rw [← indexTapeEquiv_toList m s domain X henum indices]
        simpa [indices] using hreject
      simpa [localBadIndexTapes] using hrejectIndices
    · exact (indexTapeEquiv m s domain X henum).apply_symm_apply tape

lemma card_localBadOutputs_eq_failureSet
    (m s : ℕ) (domain : ℕ → ℕ) (X : Finset ℕ)
    (henum : ReusedOriginal.Construction.MarkingMath.PrefixEnumerates m domain X)
    (N : ℕ → Finset ℕ) (B : Finset ℕ) (W : Finset ℕ) (b : ℕ) :
    (localBadOutputs m s domain N B W b).card =
      (SamplerLocalSuccess.localTrialFailureSet N B W b X s).card := by
  rw [card_localBadOutputs_eq_indexBad]
  rw [← localBadIndexTapes_image_eq_failureSet m s domain X henum N B W b]
  exact (Finset.card_image_of_injective _
    (indexTapeEquiv m s domain X henum).injective).symm

/-- The geometric ideal-draw half bound transfers to actual source draws,
including exhausted selector calls in the complement of the retry event. -/
lemma actualLocalRejectedFiber_half (m : ℕ) (hm : 0 < m)
    (t s Nbits : ℕ) (domain : ℕ → ℕ)
    (N : ℕ → Finset ℕ) (B : Finset ℕ) (W : Finset ℕ) (b : ℕ)
    (hbudget : bitBudget (fun _ => m) t 0 s ≤ Nbits)
    (hideal : 2 * (localBadOutputs m s domain N B W b).card ≤
      outputCount (fun _ => m) 0 s) :
    2 * (actualRejectedFiber m hm t s Nbits
      (localBadOutputs m s domain N B W b)).card ≤ 2 ^ Nbits := by
  classical
  apply actualRejectedFiber_half m hm t s Nbits
    (localBadOutputs m s domain N B W b) hbudget
  · intro output houtput
    exact (Finset.mem_filter.mp houtput).1
  · exact hideal

lemma local_outputCount (m d s : ℕ) :
    outputCount (fun _ => m) d s = m ^ s := by
  induction s generalizing d with
  | zero => simp [outputCount]
  | succ s ih =>
      simp only [outputCount]
      rw [ih (d + 1)]
      simp [pow_succ, Nat.mul_comm]

/-- The semantic uniform failure set supplies the exact ideal count premise
for the actual stopped-prefix law, via the source domain enumeration. -/
lemma actualLocalRejectedFiber_half_of_failureSet
    (m : ℕ) (hm : 0 < m) (t s Nbits : ℕ)
    (domain : ℕ → ℕ) (X : Finset ℕ)
    (henum : ReusedOriginal.Construction.MarkingMath.PrefixEnumerates m domain X)
    (N : ℕ → Finset ℕ) (B : Finset ℕ) (W : Finset ℕ) (b : ℕ)
    (hbudget : bitBudget (fun _ => m) t 0 s ≤ Nbits)
    (hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet N B W b X s).card ≤ X.card ^ s) :
    2 * (actualRejectedFiber m hm t s Nbits
      (localBadOutputs m s domain N B W b)).card ≤ 2 ^ Nbits := by
  apply actualLocalRejectedFiber_half m hm t s Nbits domain N B W b hbudget
  rw [card_localBadOutputs_eq_failureSet m s domain X henum N B W b,
    local_outputCount]
  have hmX : m = X.card :=
    EnumeratedDraws.prefixEnumerates_card m domain X henum
  simpa [hmX] using hhalf

/-- Under the paper's far-exception and shatter hypotheses, the actual
capped sequential local draws reject and retry on at most half of flat tapes.
This is unconditional; selector exhaustion is an abort, not a retry. -/
lemma actualLocalRejectedFiber_half_paper
    (A : Finset ℕ) (B : Finset ℕ) (N : ℕ → Finset ℕ)
    (r k c : ℕ) (choice : SamplerPhases.InitialChoice A B N r)
    (as : List ℕ) (has : as.toFinset = A) (hasNodup : as.Nodup)
    (hN : ∀ b ∈ B, N b ⊆ A)
    (hinj : ∀ b ∈ B, ∀ v ∈ B, N b = N v → b = v)
    (b : ℕ) (hb : b ∈ B)
    (hfar : 2 * k < 3 * SamplerPhases.disagreement N b
      (choice.representative b))
    (hc : 2 ≤ c)
    (hshatter : ∀ Y : Finset ℕ, Y ⊆ A → Y.Nonempty →
      (SamplerPhases.traceClasses N Y B).card ≤ c * Y.card)
    (X W : Finset ℕ) (s t Nbits : ℕ) (domain : ℕ → ℕ)
    (hX : X = (N b \ N (choice.representative b)) ∪
      (N (choice.representative b) \ N b))
    (hW : W = SamplerPhases.phase2Scan N (choice.exceptions k)
      as choice.sample)
    (hs : s = 64 * Nat.clog 2 c)
    (henum : ReusedOriginal.Construction.MarkingMath.PrefixEnumerates
      X.card domain X)
    (hpositive : 0 < X.card)
    (hbudget : bitBudget (fun _ => X.card) t 0 s ≤ Nbits) :
    2 * (actualRejectedFiber X.card hpositive t s Nbits
      (localBadOutputs X.card s domain N B W b)).card ≤ 2 ^ Nbits := by
  have hsingle := SamplerLocalSuccess.localTrial_failure_lt_half
    A B N r k c choice as has hasNodup hN hinj b hb hfar hc hshatter
  have hhalf : 2 *
      (SamplerLocalSuccess.localTrialFailureSet N B W b X s).card ≤
        X.card ^ s := by
    subst X
    subst W
    subst s
    exact Nat.le_of_lt hsingle
  exact actualLocalRejectedFiber_half_of_failureSet
    X.card hpositive t s Nbits domain X henum N B W b hbudget hhalf

/-- A source trial on a fixed flat tape exposes an actual draw trace. If its
scan rejects after all draws succeed, that tape belongs to the rejecting
fiber; an exhausted capped selector has status `2` and is excluded. -/
lemma localRepairTrial_run_flat
    {B n m domainCap s t bufferCap targetCap q b Nbits : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {X groupedB Wbase Wcurrent : Finset ℕ}
    (R : LocalRepairSource.ReadyInput B n m domainCap s t bufferCap
      targetCap q b G x X groupedB Wbase Wcurrent)
    (hL : R.σ.vars "L" = Nat.clog 2 m)
    (hv : R.σ.vars "v" = b)
    (tape : FlatTape Nbits)
    (blocks : List (Fin (Nat.clog 2 m) → Bool))
    (hbits : blocks.flatMap List.ofFn = flatBits tape)
    (hinput : R.σ.inp = FairBitRam.flattenBitBlockList blocks ++ R.rest)
    (hlen : s * t ≤ blocks.length) :
    ∃ (values : List (Fin m)) (used : ℕ) (failed : Bool)
      (σ' : Lax808846Proofs.Imp.Env),
      Lax808846Proofs.Reasoning.Run B LocalRepairSource.localRepairTrial R.σ σ'
        ((15 * Nat.clog 2 m + 30) * used + 79 * s +
          R.scanCharge (values.map (fun i => R.domain i.val)) + 38) ∧
      σ'.inp = FairBitRam.flattenBitBlockList (blocks.drop used) ++ R.rest ∧
      (failed = true → σ'.vars "repairRetryStatus" = 2) ∧
      (failed = false ∧ σ'.vars "repairRetryStatus" = 0 →
        tape ∈ actualRejectedFiber m R.hpositive t s Nbits
          (localBadOutputs m s R.domain (ExceptionPhaseSource.numericNeighborhood G)
            groupedB Wbase b)) := by
  obtain ⟨values, used, failed, σ', htrace, hrun, hinp, _, _, _, _, _, _, _,
      hfail, _, hsuccess⟩ :=
    LocalRepairSource.localRepairTrial_run_blocks R hL hv blocks R.rest hinput hlen
  refine ⟨values, used, failed, σ', hrun, hinp, ?_, ?_⟩
  · intro hf
    exact (hfail hf).1
  · rintro ⟨hf, hstatus⟩
    have hnot : ¬ SamplerPhases.localTrialIsolates
        (ExceptionPhaseSource.numericNeighborhood G) groupedB Wbase b
        (values.map (fun i => R.domain i.val)) := by
      intro hiso
      have hs := (hsuccess hf).1.mpr hiso
      omega
    have hvalid : values.map Fin.val ∈
        outputVectors (fun _ => m) (fun _ => 0) 0 s := by
      obtain ⟨attempts, hflat⟩ :=
        drawTrace_success_to_flat m R.hpositive t 0 htrace hf
      exact ValidOutput.mem_outputVectors (fun _ => m) (fun _ => 0)
        (ValidPath.validOutput (fun _ => m) t (fun _ => 0)
          (FlatClassSuccess.validPath (fun _ => m) t (fun _ => 0) hflat))
    have hbad : values.map Fin.val ∈ localBadOutputs m s R.domain
        (ExceptionPhaseSource.numericNeighborhood G) groupedB Wbase b := by
      simp only [localBadOutputs, Finset.mem_filter]
      constructor
      · exact hvalid
      · simpa [List.map_map, Function.comp_def] using hnot
    apply Finset.mem_biUnion.mpr
    refine ⟨values.map Fin.val, hbad, ?_⟩
    simp only [actualDrawOutputFiber, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact ⟨blocks, values, used, hbits, by simpa [hf] using htrace, rfl⟩

end
end Lax457868Proofs.LocalFlatLaw
