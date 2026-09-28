import Lax235315Proofs.Construction.SampledGoodBranch
import Lax235315Proofs.Construction.CanonicalLiteralSampleGood
import Lax235315Proofs.Construction.SourceAdaptiveState
import Lax235315Proofs.Construction.HistoryRoundSource
import Mathlib.Tactic

set_option maxHeartbeats 4000000

/-! A nonfailing block of the actual source tape makes the literal sampled
round take its accepted dispatch path. -/

namespace Lax235315Proofs.Construction.LiteralGoodDispatch

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.CollisionDetection
open Lax235315Proofs.Construction.GoodRoundBits
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NearCounterCorrectness
open Lax235315Proofs.Construction.PackedKeys
open Lax235315Proofs.Construction.PartitionSource
open Lax235315Proofs.Construction.PositionFailureBits
open Lax235315Proofs.Construction.ReductionRoundSource
open Lax235315Proofs.Construction.RandomKeyEquiv
open Lax235315Proofs.Construction.RandomKeysRead
open Lax235315Proofs.Construction.ReadKeys
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.SampledGoodBranch
open Lax235315Proofs.Construction.Sampling
open Lax235315Proofs.Construction.ScanSampleTransport
open Lax235315Proofs.Construction.ScanIndexEquiv
open Lax235315Proofs.Construction.TapeBlocks
open Lax235315Proofs.Construction.TapeKeyAgreement
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.TracePartitions
open Lax235315Proofs.Construction.GraphSampling
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.GuardedArithmetic
open Lax235315Proofs.Construction.PositionFailureBounds
open Lax195003.WordRamRandomness
open Lax235315Proofs.Construction.GraphAdaptiveProtocol
open Lax235315Proofs.Construction.GuardedAdaptiveProtocol
open Lax235315Proofs.Construction.HistoryRoundSource
open Lax235315Proofs.Construction.SourceAdaptiveState

noncomputable section

private lemma noAdjacent_of_injective_assignment
    {n L : ℕ} {active : ℕ → ℕ}
    (hL : 0 < L)
    (ρ : Fin (((activeVertices n active).card * 8) * L) → Bool)
    (hinj : Function.Injective
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ))
    {digits : Fin 8 → ℕ → ℕ} {sorted : List ℕ}
    (hsortedDef : sorted = radixSort8 (2 ^ Nat.clog 2 n) digits
      (scanList active 0 n))
    (hkeyBound : ∀ d v, v ∈ scanList active 0 n →
      digits d v < 2 ^ Nat.clog 2 n)
    (hactiveKey : ∀ v : ActiveVertex n active,
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm v)).val =
        packedKey (2 ^ L) digits v.val.val) :
    ¬ HasAdjacentEqualDigits digits sorted := by
  intro hadj
  rcases hadj with ⟨j, hj₁, hjlen, hdigits⟩
  have hperm : List.Perm sorted (scanList active 0 n) := by
    rw [hsortedDef]
    exact radixSort8_perm (scanList_nodup active 0 n) hkeyBound
  have hnodup : sorted.Nodup := hperm.symm.nodup (scanList_nodup active 0 n)
  have hprev : j - 1 < sorted.length := by omega
  let u := sorted.getD (j - 1) 0
  let v := sorted.getD j 0
  have huGet : sorted.getD (j - 1) 0 = sorted[j - 1] :=
    List.getD_eq_getElem _ _ hprev
  have hvGet : sorted.getD j 0 = sorted[j] :=
    List.getD_eq_getElem _ _ hjlen
  have huMem : u ∈ scanList active 0 n := by
    change sorted.getD (j - 1) 0 ∈ scanList active 0 n
    rw [huGet]
    exact hperm.subset (List.getElem_mem hprev)
  have hvMem : v ∈ scanList active 0 n := by
    change sorted.getD j 0 ∈ scanList active 0 n
    rw [hvGet]
    exact hperm.subset (List.getElem_mem hjlen)
  have hpack : packedKey (2 ^ L) digits u = packedKey (2 ^ L) digits v := by
    unfold packedKey
    rw [(digitList_eq_iff).2 hdigits]
  have huSpec := mem_scanList.mp huMem
  have hvSpec := mem_scanList.mp hvMem
  let huActive : ActiveVertex n active := ⟨⟨u, by omega⟩, huSpec.2.2⟩
  let hvActive : ActiveVertex n active := ⟨⟨v, by omega⟩, hvSpec.2.2⟩
  have hpack' : packedKey (2 ^ L) digits huActive.val.val =
      packedKey (2 ^ L) digits hvActive.val.val := by
    simpa [huActive, hvActive] using hpack
  have hassignValue :
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm huActive)).val =
      (roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm hvActive)).val := by
    calc
      _ = packedKey (2 ^ L) digits huActive.val.val := hactiveKey huActive
      _ = packedKey (2 ^ L) digits hvActive.val.val := hpack'
      _ = _ := (hactiveKey hvActive).symm
  have hassign :
      roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm huActive) =
      roundAssignmentEquiv (activeVertices n active).card L hL ρ
        ((scanIndexEquiv active n).symm hvActive) := Fin.ext hassignValue
  have hindex := hinj hassign
  have huv : u = v := by
    have hvertices := congrArg (scanIndexEquiv active n) hindex
    simpa [huActive, hvActive] using
      congrArg (fun w : ActiveVertex n active => w.val.val) hvertices
  have hget : sorted.get ⟨j - 1, hprev⟩ = sorted.get ⟨j, hjlen⟩ := by
    rw [List.get_eq_getElem, List.get_eq_getElem]
    calc
      sorted[j - 1] = u := huGet.symm
      _ = v := huv
      _ = sorted[j] := hvGet
  have hsameIndex := (hnodup.get_inj_iff).mp hget
  have hsameIndexVal := congrArg Fin.val hsameIndex
  change j - 1 = j at hsameIndexVal
  omega

/-- A nonfailing block of the actual binary input tape forces the sampled
source round to set the good flag and take the successful dispatch branch. -/
lemma samplingFrontier_good_literal_bits_dispatch
    {B c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)} {σ : Env}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (h : Frontier B c n x σ)
    (hc : 1 ≤ c) (hn : 1 < n)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount")
    (hcsq : σ.vars "csq" = c ^ 2)
    (hbound : σ.vars "nearBound" = 6 * c ^ 2 * Nat.clog 2 n)
    (htape : 8 * Nat.clog 2 n * σ.vars "acount" ≤ σ.inp.length)
    (hqB : 2 ^ Nat.clog 2 n < B)
    (hnB : 2 * n + 1 < B) (htargetB : 2 * edgeCount x < B)
    (hdenomB : 2 * c ^ 2 < B)
    (hboundB : 6 * c ^ 2 * Nat.clog 2 n < B)
    (hgoodBits : sourceBoolTape σ.inp
        (((activeVertices n (view σ "activeA")).card * 8) * Nat.clog 2 n) ∉
      badRoundBits (activeVertices n (view σ "activeA")).card
        (Nat.clog 2 n) (sampleSize (σ.vars "acount") c)
        (Nat.clog_pos (by omega) hn)
        (badPositionSamples (view σ "activeA") n
          (familyBadSamples
            (traceFamily G (activeFinset (view σ "activeA"))
              (activeFinset (view σ "activeB"))) id
            (activeFinset (view σ "activeA")) c (Nat.clog 2 n)))) :
    ∃ bits : ℕ → Fin 8 → List ℕ, ∃ τ : Env, ∃ ord : ℕ → ℕ, ∃ τ' : Env,
      Run B SamplingPrefixSource.samplingPrefix σ τ
        ((120 * n + 120 * Nat.clog 2 n * σ.vars "acount" + 8) +
          512 * (σ.vars "acount" + 2 ^ Nat.clog 2 n + 1) +
          300 * (σ.vars "acount" + 1)) ∧
      PrefixEnumerates (sampleSize (σ.vars "acount") c) ord
        ((RadixMath.radixSort8 (2 ^ Nat.clog 2 n)
          (ReadKeys.filledKey (fun d => view σ (RandomKeysRead.keyName d))
            (view σ "activeA") bits n)
          (ReadKeys.scanList (view σ "activeA") 0 n)).take
            (sampleSize (σ.vars "acount") c)).toFinset ∧
      τ.vars "collision" = 0 ∧
      Run B dispatchRound τ τ' (2300 * (x.length + 1) + 4) ∧
      τ'.vars "good" = 1 ∧ Frontier B c n x τ' ∧
      τ'.vars "round" = τ.vars "round" + 1 ∧
      τ'.vars "acount" ≤ τ.vars "acount" / 2 + c ^ 2 := by
  let active := view σ "activeA"
  let L := Nat.clog 2 n
  let a := (activeVertices n active).card
  let ρ := sourceBoolTape σ.inp ((a * 8) * L)
  let original : Fin 8 → ℕ → ℕ := fun d => view σ (keyName d)
  have hL : 0 < L := Nat.clog_pos (by omega) hn
  have ha : 0 < σ.vars "acount" := by
    rw [h.activeCount]
    exact Finset.card_pos.mpr (h.nonemptyA (by omega))
  have hs : sampleSize (σ.vars "acount") c ≤ a := by
    simpa [a, active, h.activeCount] using sampleSize_le_self hc ha
  have hlen : 8 * L * (scanList active 0 n).length ≤ σ.inp.length := by
    rw [scanList_length_eq_activeVertices_card active n]
    have hac : (activeVertices n active).card = σ.vars "acount" := by
      simpa [active] using h.activeCount.symm
    rw [hac]
    simpa [L, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using htape
  obtain ⟨bits, τ, ord, hsampleRun, hfront, hord, hprefix, hcollisionEq,
      hbitsCanonical, hkeyBound, hsortedBound, hrange, hsubset, hcard,
      hdispatch⟩ :=
    SampledGoodBranch.samplingFrontier_good_sample_dispatch hx hG h hc hn
      hlarge hcsq hbound htape hqB hnB htargetB hdenomB hboundB
  have hgood : ρ ∉ badRoundBits a L (sampleSize (σ.vars "acount") c) hL
      (badPositionSamples active n
        (familyBadSamples
          (traceFamily G (activeFinset (view σ "activeA"))
            (activeFinset (view σ "activeB"))) id
          (activeFinset (view σ "activeA")) c L)) := by
    simpa [ρ, a, L, active, hL] using hgoodBits
  have hkeyBoundCanon : ∀ d v, v ∈ scanList active 0 n →
      filledKey original active (scanTapeBits active L σ.inp) n d v < 2 ^ L := by
    simpa [original, active, L, hbitsCanonical] using hkeyBound
  have hsortedBoundCanon : ∀ v ∈ radixSort8 (2 ^ L)
      (filledKey original active (scanTapeBits active L σ.inp) n)
      (scanList active 0 n), ∀ d,
        filledKey original active (scanTapeBits active L σ.inp) n d v < 2 ^ L := by
    simpa [original, active, L, hbitsCanonical] using hsortedBound
  have hsampleGood :=
    CanonicalLiteralSampleGood.canonical_source_sample_good_of_nonfailing_bits
      hL hn rfl h.workspace.randomInput hlen original
      (familyBadSamples
        (traceFamily G (activeFinset (view σ "activeA"))
          (activeFinset (view σ "activeB"))) id
        (activeFinset (view σ "activeA")) c L)
      hsortedBoundCanon hkeyBoundCanon hs hgood
  have hcollision0 : τ.vars "collision" = 0 := by
    have hnoadj :=
      noAdjacent_of_injective_assignment
        hL ρ (by
          obtain ⟨f, hf, _⟩ := good_assignment_of_not_badRoundBits a L
            (sampleSize (σ.vars "acount") c) hL
            (badPositionSamples active n
              (familyBadSamples
                (traceFamily G (activeFinset (view σ "activeA"))
                  (activeFinset (view σ "activeB"))) id
                (activeFinset (view σ "activeA")) c L)) ρ hgood
          rw [← hf]
          exact f.2)
        (by rfl) hkeyBoundCanon
        (canonical_filledKey_activeKey hL h.workspace.randomInput hlen original)
    have hnoadjActual : ¬ HasAdjacentEqualDigits
        (filledKey original active bits n)
        (radixSort8 (2 ^ L) (filledKey original active bits n)
          (scanList active 0 n)) := by
      simpa [active, L, hbitsCanonical] using hnoadj
    rw [hcollisionEq]
    simp [hnoadjActual, active, L, original]
  have hactiveAτ : activeFinset (n := n) (view τ "activeA") =
      activeFinset (n := n) active := by
    have har := hsampleRun.frame_arr "activeA" (by decide)
    have hv : view τ "activeA" = active := by
      funext i
      simp [view, active, har]
    rw [hv]
  have hactiveBτ : activeFinset (n := n) (view τ "activeB") =
      activeFinset (n := n) (view σ "activeB") := by
    have har := hsampleRun.frame_arr "activeB" (by decide)
    have hv : view τ "activeB" = view σ "activeB" := by
      funext i
      simp [view, har]
    rw [hv]
  let W := ((RadixMath.radixSort8 (2 ^ Nat.clog 2 n)
    (ReadKeys.filledKey (fun d => view σ (RandomKeysRead.keyName d))
      (view σ "activeA") bits n)
    (ReadKeys.scanList (view σ "activeA") 0 n)).take
      (sampleSize (σ.vars "acount") c)).toFinset
  have hbadσ : NumericSampleLift.finSample n W ∉
      familyBadSamples
        (traceFamily G (activeFinset (view σ "activeA"))
          (activeFinset (view σ "activeB"))) id
        (activeFinset (view σ "activeA")) c L := by
    simpa [W, active, L, original, hbitsCanonical] using hsampleGood.2.2
  have hbadτ : SampledGoodBranch.finSample n W ∉
      familyBadSamples
        (traceFamily G (activeFinset (view τ "activeA"))
          (activeFinset (view τ "activeB"))) id
        (activeFinset (view τ "activeA")) c L := by
    have hfin : SampledGoodBranch.finSample n W = NumericSampleLift.finSample n W := by
      ext v
      simp [SampledGoodBranch.finSample, NumericSampleLift.finSample]
    simpa [hfin, hactiveAτ, hactiveBτ] using hbadσ
  obtain ⟨τ', hdispatchRun, hgoodτ, hfrontτ, hroundτ, hacountτ⟩ :=
    hdispatch hcollision0 (by simpa [W, L] using hbadτ)
  exact ⟨bits, τ, ord, τ', hsampleRun, hprefix, hcollision0,
    hdispatchRun, hgoodτ, hfrontτ, hroundτ, hacountτ⟩

end

private lemma sourceBoolTape_bitTape {K : ℕ} (η : Fin K → Bool) :
    sourceBoolTape (bitTape η) K = η := by
  funext i
  simp [TapeKeyAgreement.sourceBoolTape, bitTape]

noncomputable section

set_option maxHeartbeats 8000000

/-- Every block outside the adaptive source's concrete bad-block set makes
the chosen one-round output accepted and leaves `good = 1`. The actual input
round is the literal `bitTape` block. -/
lemma source_good_block_accepted
    {c n : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (s : RoundState c n x G)
    (bits : Fin (sourceWidth (some s)) → Bool)
    (hgood : bits ∉ sourceBad (G := G) (x := x) (c := c)
      (Nat.clog_pos (by omega) s.nontrivial) (some s)) :
    Accepted s (roundOutput s hx hG hc bits) ∧
      (roundOutput s hx hG hc bits).vars "good" = 1 := by
  let L := Nat.clog 2 n
  let input := withBlock s bits
  have hL : 0 < L := Nat.clog_pos (by omega) s.nontrivial
  have hK : sourceWidth (some s) =
      ((activeVertices n (view s.env "activeA")).card * 8) * L := by
    simpa [L] using SourceAdaptiveState.sourceWidth_some s
  have hρgoodBlock : sourceBoolTape (input.inp)
      (((activeVertices n (view s.env "activeA")).card * 8) * L) ∉
      GraphAdaptiveProtocol.badBlock G c L hL
        (toGuardedState s).toGraphQueryState := by
    change bits ∉ GraphAdaptiveProtocol.badBlock G c L hL
      (toGuardedState s).toGraphQueryState at hgood
    have hρ : sourceBoolTape input.inp
        (((activeVertices n (view s.env "activeA")).card * 8) * L) = bits := by
      change sourceBoolTape (bitTape bits) (sourceWidth (some s)) = bits
      exact sourceBoolTape_bitTape bits
    rw [hρ]
    exact hgood
  have hρgood : sourceBoolTape (input.inp)
      (((activeVertices n (view s.env "activeA")).card * 8) * L) ∉
      badRoundBits (activeVertices n (view s.env "activeA")).card L
        (sampleSize ((activeFinset (n := n) (view s.env "activeA")).card) c) hL
        (badPositionSamples (view s.env "activeA") n
          (familyBadSamples
            (traceFamily G (activeFinset (view s.env "activeA"))
              (activeFinset (view s.env "activeB"))) id
            (activeFinset (view s.env "activeA")) c L)) := by
    exact hρgoodBlock
  have hρgood' : sourceBoolTape (input.inp)
      (((activeVertices n (view s.env "activeA")).card * 8) * L) ∉
      badRoundBits (activeVertices n (view s.env "activeA")).card L
        (sampleSize (s.env.vars "acount") c) hL
        (badPositionSamples (view s.env "activeA") n
          (familyBadSamples
            (traceFamily G (activeFinset (view s.env "activeA"))
              (activeFinset (view s.env "activeB"))) id
            (activeFinset (view s.env "activeA")) c L)) := by
    have heq : s.env.vars "acount" =
        (activeFinset (n := n) (view s.env "activeA")).card := by
      rw [s.frontier.activeCount, ← activeFinset_card_eq_activeVertices
        (view s.env "activeA") n]
    simpa only [heq] using hρgood
  have hqB : 2 ^ Nat.clog 2 n < sourceBound c x := by
    obtain ⟨_, _, _, hqB, _, _, _, _⟩ := source_fits_of_square_le hx hc
      s.nontrivial (square_le_vertices s)
    exact hqB
  have hnB : 2 * n + 1 < sourceBound c x := by
    obtain ⟨_, _, _, _, hnB, _, _, _⟩ := source_fits_of_square_le hx hc
      s.nontrivial (square_le_vertices s)
    exact hnB
  have htargetB : 2 * edgeCount x < sourceBound c x := by
    obtain ⟨_, _, _, _, _, htargetB, _, _⟩ := source_fits_of_square_le hx hc
      s.nontrivial (square_le_vertices s)
    exact htargetB
  have hdenomB : 2 * c ^ 2 < sourceBound c x := by
    obtain ⟨_, _, _, _, _, _, _, hdenomB⟩ := source_fits_of_square_le hx hc
      s.nontrivial (square_le_vertices s)
    exact hdenomB
  have hacountLe : s.env.vars "acount" ≤ n := by
    rw [s.frontier.activeCount]
    exact activeVertices_card_le _ _
  have hboundB : 6 * c ^ 2 * Nat.clog 2 n < sourceBound c x := by
    have hthresholdB : 12 * c ^ 2 * Nat.clog 2 n < sourceBound c x :=
      lt_trans (lt_of_lt_of_le s.large hacountLe)
        (by simpa only [s.frontier.workspace.vertices] using
          s.frontier.workspace.bounded.vars "n")
    nlinarith
  have hfrontInput : Frontier (sourceBound c x) c n x input :=
    frontier_withBlock s bits (by dsimp [sourceBound]; omega)
  have hinputTape : 8 * L * input.vars "acount" ≤ input.inp.length := by
    have hlenBits : (bitTape bits).length = 8 * L * s.env.vars "acount" := by
      calc
        (bitTape bits).length = sourceWidth (some s) :=
          RandomKeyEquiv.bitTape_length bits
        _ = 8 * L * s.env.vars "acount" := by
          rw [SourceAdaptiveState.sourceWidth_some, s.frontier.activeCount]
          dsimp [L]
          ring
    calc
      8 * L * input.vars "acount" = 8 * L * s.env.vars "acount" := by
        simp [input, withBlock, withInput]
      _ = (bitTape bits).length := hlenBits.symm
      _ ≤ s.env.inp.length + (bitTape bits).length := Nat.le_add_left _ _
      _ = input.inp.length := by simp [input, withBlock, withInput, s.emptyInput]
  have hsampled := samplingFrontier_good_literal_bits_dispatch hx hG hfrontInput hc
    s.nontrivial s.large s.square s.nearBound hinputTape hqB hnB htargetB
    hdenomB hboundB hρgood'
  rcases hsampled with ⟨sampleBits, τ, ord, τ', hsampleRun, hprefix,
    hcollision, hdispatch, hgoodτ, hfrontτ, hroundτ, hacountτ⟩
  have hfull : Run (sourceBound c x) reductionRound input τ'
      ((120 * n + 120 * Nat.clog 2 n * input.vars "acount" + 8) +
        512 * (input.vars "acount" + 2 ^ Nat.clog 2 n + 1) +
        300 * (input.vars "acount" + 1) +
        (2300 * (x.length + 1) + 4)) :=
    ReductionRoundSource.sampling_dispatch hsampleRun hdispatch
  have hfull' : Run (sourceBound c x) reductionRound (withBlock s bits) τ'
      ((120 * n + 120 * Nat.clog 2 n * input.vars "acount" + 8) +
        512 * (input.vars "acount" + 2 ^ Nat.clog 2 n + 1) +
        300 * (input.vars "acount" + 1) +
        (2300 * (x.length + 1) + 4)) := by
    simpa [input] using hfull
  obtain ⟨_, _, hfullStep⟩ := hfull'
  have hspec := roundOutput_spec s hx hG hc bits
  obtain ⟨_, _, hspecStep⟩ := hspec.1
  have hroundOutput : roundOutput s hx hG hc bits = τ' :=
    (BigStep.unique hspecStep.bigStep hfullStep.bigStep).1
  obtain ⟨τstore, hstoredRun, _hstoreWorkspace, _hstoreInput, hstoredOutcome⟩ :=
    HistoryRoundSource.reductionRound_run_stored hx hG hfrontInput
      (stored_withBlock s bits) hc s.nontrivial s.large s.square s.nearBound
      hinputTape hqB hnB htargetB hdenomB hboundB
  obtain ⟨_, _, hstoredStep⟩ := hstoredRun
  have hstoreEq : τ' = τstore :=
    (BigStep.unique hfullStep.bigStep hstoredStep.bigStep).1
  have hgoodStore : τstore.vars "good" = 1 := by
    rw [← hstoreEq]
    exact hgoodτ
  have hacceptedStore : Accepted s τstore := by
    rcases hstoredOutcome with ⟨hstoreFront, hstoreRound, hstoreCount, hstored⟩ | hreject
    · refine ⟨hstoreFront, ?_, ?_, hstored⟩
      · simpa [input, withBlock, withInput] using hstoreRound
      · simpa [input, withBlock, withInput] using hstoreCount
    · exact (hreject.1 hgoodStore).elim
  constructor
  · rw [hroundOutput, hstoreEq]
    exact hacceptedStore
  · rw [hroundOutput]
    exact hgoodτ

end

set_option maxHeartbeats 4000000

end Lax235315Proofs.Construction.LiteralGoodDispatch
