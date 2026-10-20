import Lax457868Proofs.PrepareRefinedRound
import Lax457868Proofs.RefinedSetup
import Lax457868Proofs.CompleteSamplerSource

/-! Factual round workspace to the existing complete-sampler interface.
The adapter executes the two packing scans and runtime parameter assignments;
it does not postulate their resulting register values. -/

namespace Lax457868Proofs.RefinedRoundInput

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.WelzlSetup
open Lax457868Proofs.ReusedOriginal.Construction.RadixEight
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.PrepareRefinedRound
open Lax457868Proofs.SamplerRuntimeSetup
open Lax457868Proofs.InitialSamplerRetriesSource
open Lax457868Proofs.CompleteSamplerSource

/-- The five mark arrays cleared by every completed sampler execution. -/
def repairMarks : List String :=
  ["trialActive", "trialRowMarks", "trialDesiredMarks", "repairBMarks", "repairRMarks"]

/-- Source facts carried between rounds; no random experiment or successful
sample appears among the fields. -/
structure RoundData (c n : ℕ) (x : List ℕ) (A C : Finset ℕ) (σ : Env) : Prop where
  parameter : σ.vars "c" = c
  vertices : σ.vars "n" = n
  radixSize : σ.vars "qpow" = 2 ^ Nat.clog 2 n
  cutoff : σ.vars "cutoffResult" = 2 * refinedCutoffK c
  logParameter : σ.vars "refinedLogC" = Nat.clog 2 c
  offsets : σ.arrs "off" = arrOf (n + 1) (offset x)
  targets : σ.arrs "tgt" = arrOf (2 * edgeCount x) (target x)
  activeA : σ.arrs "activeA" = arrOf n (setFlag A)
  activeB : σ.arrs "activeB" = arrOf n (setFlag C)
  lengths : ∀ a, (σ.arrs a).length = welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n) a
  cleared : ∀ a ∈ repairMarks, σ.arrs a = arrOf n (fun _ => 0)
  nextA_bits : ∀ v ∈ σ.arrs "nextA", v ≤ 1
  nextB_bits : ∀ v ∈ σ.arrs "nextB", v ≤ 1

/-- The deterministic input setup establishes the first round's workspace. -/
lemma initial_roundData {c n : ℕ} {x bits : List ℕ} {σ : Env}
    (R : RefinedSetup.Ready c n x bits σ)
    (hlarge : 2 * refinedCutoffK c < n) :
    RoundData c n x (Finset.range n) (Finset.range n) σ := by
  have hflags : arrOf n (fun _ => 1) = arrOf n (setFlag (Finset.range n)) := by
    apply arrOf_congr
    intro v hv
    simp [setFlag, Finset.mem_range.mpr hv]
  refine ⟨R.parameter, R.vertices, R.radixSize, ?_, R.logParameter hlarge,
    R.offsets, R.targets, R.activeA.trans hflags, R.activeB.trans hflags,
    R.lengths, ?_, ?_, ?_⟩
  · rw [R.cutoff, Nat.min_eq_right hlarge.le]
  · intro a ha
    have hne (b : String) (hb : b ∉ repairMarks) : a ≠ b := by
      intro h; subst a; exact hb ha
    rw [R.scratch a (hne _ (by simp [repairMarks])) (hne _ (by simp [repairMarks]))
      (hne _ (by simp [repairMarks])) (hne _ (by simp [repairMarks]))]
    simp [welzlExt, hne "off" (by simp [repairMarks]),
      hne "tgt" (by simp [repairMarks]), hne "count" (by simp [repairMarks]), arrOf]
  · intro v hv
    rw [R.scratch "nextA" (by decide) (by decide) (by decide) (by decide)] at hv
    have hz : v = 0 := (List.mem_replicate.mp hv).2
    omega
  · intro v hv
    rw [R.scratch "nextB" (by decide) (by decide) (by decide) (by decide)] at hv
    have hz : v = 0 := (List.mem_replicate.mp hv).2
    omega

/-- Actual preparation supplies every field required by the complete sampler.
The only random input premise is a sufficiently long fair-bit prefix. -/
lemma prepare_sampler_input {B c n : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {A C : Finset ℕ} {σ : Env} {bits : List Bool} {rest : List ℕ}
    (D : RoundData c n x A C σ) (hx : EncodesGraph x n G)
    (hc : 2 ≤ c) (hA : A ⊆ Finset.range n) (hC : C ⊆ Finset.range n)
    (hlarge : 2 * refinedCutoffK c < A.card)
    (hB : 4 * (x.length + 1) ≤ B)
    (hinput : σ.inp = bits.map Bool.toNat ++ rest)
    (hbudget : (A.card / (4 * c ^ 2)) * n * Nat.clog 2 A.card +
      n * n * Nat.clog 2 n ≤ bits.length) :
    ∃ R : ReadyInput B n A.card n (A.card / (4 * c ^ 2)) n n
        (2 * edgeCount x) (2 ^ Nat.clog 2 n) (refinedCutoffK c)
        (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) G x A,
      ∃ _S : RuntimeInput R (64 * Nat.clog 2 c) n,
      Run B prepareRefinedRound σ R.I.σ (40 * n + 58) ∧
      R.I.bits = bits ∧ R.I.rest = rest ∧ R.I.activeB = setFlag C ∧
      R.I.σ.vars "initialRetryCap" = n ∧
      (∀ a, a ≠ "ord" → a ≠ "drawDomain" → R.I.σ.arrs a = σ.arrs a) := by
  classical
  have hAn : A.card ≤ n := by simpa using Finset.card_le_card hA
  have hlargeN : 2 * refinedCutoffK c < n := hlarge.trans_le hAn
  have hlen := hx.length_eq
  have hnB : n < B := by omega
  have hn2B : 2 * n + 1 < B := by omega
  have htargetB : 2 * edgeCount x < B := by omega
  have hpowN : 2 ^ Nat.clog 2 n < B := by
    have h := ReusedOriginal.Construction.DriverSetup.radix_size_lt n
    omega
  have hpowA : 2 ^ Nat.clog 2 A.card < B :=
    (Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 hAn)).trans_lt hpowN
  have hApos : 0 < A.card := by omega
  have hAnonempty : A.Nonempty := Finset.card_pos.mp hApos
  have hrn : A.card / (4 * c ^ 2) ≤ n := (Nat.div_le_self _ _).trans hAn
  have hcapn : A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1)) ≤ n :=
    (Nat.div_le_self _ _).trans hAn
  obtain ⟨_, _, hs, _, _, h64⟩ := parameter_bounds hc hlargeN
  obtain ⟨ord, hord⟩ := exists_arrOf_of_length
    (show (σ.arrs "ord").length = n by simpa [welzlExt] using D.lengths "ord")
  obtain ⟨domain, hdomain⟩ := exists_arrOf_of_length
    (show (σ.arrs "drawDomain").length = n by simpa [welzlExt] using D.lengths "drawDomain")
  obtain ⟨τ, packed, hrun, hpacked, henum, hmod, hbcount, hr, hsample, hcap,
      hnear, hfar, hicap, hrcap, hdcap, hfa, hfv, hin, hout⟩ :=
    prepareRefinedRound_run D.vertices D.parameter D.logParameter D.cutoff
      hA hC D.activeA D.activeB hord hdomain hc hlargeN hnB
  have htlength (a : String) : (τ.arrs a).length =
      welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n) a := by
    rw [run_array_length_eq hrun a]
    exact D.lengths a
  have hrepr : ∀ a, ∃ f : ℕ → ℕ,
      τ.arrs a = arrOf (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n) a) f :=
    fun a => exists_arrOf_of_length (htlength a)
  choose f hf using hrepr
  have hreprN (a : String) (h₁ : a ≠ "off") (h₂ : a ≠ "tgt")
      (h₃ : a ≠ "count") : τ.arrs a = arrOf n (f a) := by
    simpa [welzlExt, h₁, h₂, h₃] using hf a
  have hcleared (a : String) (ha : a ∈ repairMarks) :
      τ.arrs a = arrOf n (fun _ => 0) := by
    rw [hfa a (by intro h; subst a; simp [repairMarks] at ha)
      (by intro h; subst a; simp [repairMarks] at ha)]
    exact D.cleared a ha
  have hCeq : activeVertices n (setFlag C) = C :=
    flagged_setFlag hC
  let I : InitialSamplerAttempt.Input B n A.card n (A.card / (4 * c ^ 2)) n n
      (2 * edgeCount x) (2 ^ Nat.clog 2 n) G x A := {
    σ := τ
    key0 := f "key0", domain := packed, oldDraws := f "sampleDraws"
    oldFlags := f "sampleFlags", ord := f "ord", activeB := setFlag C
    classB := f "classB", classSize := f "classSize", markedCount := f "markedCount"
    stamp := f "stamp", marked := f "marked", touched := f "touched", split := f "split"
    repB := f "repB", count := f "count", scratchOrder := f "scratchOrder"
    repClass := f "repClass", bits := bits, rest := rest, hx := hx
    htargetCapEq := rfl, henum := henum, hAnonempty := hAnonempty, hA := hA
    hn := (hfv _ (by decide)).trans D.vertices
    hQpow := (hfv _ (by decide)).trans D.radixSize
    hactiveBCount := by simpa [hCeq] using hbcount
    hdrawModulus := hmod, hbatchTarget := hr, hdrawCap := hdcap
    hinput := hin.trans hinput
    hkey0 := hreprN _ (by decide) (by decide) (by decide)
    hdrawDomain := hpacked
    hsampleDraws := hreprN _ (by decide) (by decide) (by decide)
    hsampleFlags := hreprN _ (by decide) (by decide) (by decide)
    hord := hreprN _ (by decide) (by decide) (by decide)
    hoff := (hfa _ (by decide) (by decide)).trans D.offsets
    htarget := (hfa _ (by decide) (by decide)).trans D.targets
    hactiveB := (hfa _ (by decide) (by decide)).trans D.activeB
    hclassB := hreprN _ (by decide) (by decide) (by decide)
    hclassSize := hreprN _ (by decide) (by decide) (by decide)
    hmarkedCount := hreprN _ (by decide) (by decide) (by decide)
    hstamp := hreprN _ (by decide) (by decide) (by decide)
    hmarked := hreprN _ (by decide) (by decide) (by decide)
    htouched := hreprN _ (by decide) (by decide) (by decide)
    hsplit := hreprN _ (by decide) (by decide) (by decide)
    hrepB := hreprN _ (by decide) (by decide) (by decide)
    hcount := by simpa [welzlExt] using hf "count"
    hscratch := hreprN _ (by decide) (by decide) (by decide)
    hrepClass := hreprN _ (by decide) (by decide) (by decide)
    hactive01 := by intro v hv; simp [setFlag]; split_ifs <;> omega
    hQle := Nat.le_pow_clog (by decide) n
    hQltB := hpowN, hnPlusOneB := by omega
    htargetCapB := htargetB, hrBuf := hrn, hrB := hrn.trans_lt hnB
    htB := hnB, hmPos := hApos, hmCap := hAn, hmB := hAn.trans_lt hnB
    htwoB := by omega, honeB := by omega, hpowM := hpowA, hpowN := hpowN
    hbudget := hbudget }
  let R : ReadyInput B n A.card n (A.card / (4 * c ^ 2)) n n
      (2 * edgeCount x) (2 ^ Nat.clog 2 n) (refinedCutoffK c)
      (A.card / (4 * c ^ 2 * (64 * Nat.clog 2 c + 1))) G x A := {
    I := I, degree := f "degree", inter := f "inter", neighbors := f "neighbors"
    exceptionFlags := f "exceptionFlags", exceptionList := f "exceptionList"
    hactiveA := (hfa _ (by decide) (by decide)).trans D.activeA
    hdegree := hreprN _ (by decide) (by decide) (by decide)
    hinter := hreprN _ (by decide) (by decide) (by decide)
    hneighbors := hreprN _ (by decide) (by decide) (by decide)
    hexceptionFlags := hreprN _ (by decide) (by decide) (by decide)
    hexceptionList := hreprN _ (by decide) (by decide) (by decide)
    hnearBound := hnear, hexceptionCap := hcap, hnB := hn2B
    hkB := (Nat.div_le_self _ _).trans_lt (by omega)
    hcapB := hcapn.trans_lt hnB }
  let S : RuntimeInput R (64 * Nat.clog 2 c) n := {
    hdomainCap := rfl, hsampleSize := hsample, hrepairCap := hrcap
    hfarBound := hfar
    hstartLength := by simpa [welzlExt] using htlength "repairClassStart"
    htrialZero := hcleared _ (by simp [repairMarks])
    hrowZero := hcleared _ (by simp [repairMarks])
    hdesiredZero := hcleared _ (by simp [repairMarks])
    hrowLength := by simpa [welzlExt] using htlength "trialRowList"
    hdesiredLength := by simpa [welzlExt] using htlength "trialDesiredList"
    hdiffLength := by simpa [welzlExt] using htlength "trialDiffList"
    hBListLength := by simpa [welzlExt] using htlength "repairBList"
    hRListLength := by simpa [welzlExt] using htlength "repairRList"
    hBMarksZero := hcleared _ (by simp [repairMarks])
    hRMarksZero := hcleared _ (by simp [repairMarks])
    hsBuffer := hs.le, hsB := hs.trans hnB, hrepairCapB := hnB
    hfarB := (Nat.div_le_self _ _).trans_lt (hlargeN.trans hnB) }
  exact ⟨R, S, hrun, rfl, rfl, rfl, hicap, hfa⟩

end Lax457868Proofs.RefinedRoundInput
