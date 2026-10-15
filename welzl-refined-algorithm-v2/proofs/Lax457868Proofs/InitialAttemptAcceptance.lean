import Lax457868Proofs.BatchedDistances
import Lax457868Proofs.ExceptionCollection
import Lax457868Proofs.SamplePacking
import Lax457868Proofs.SamplerPhases
import Lax457868Proofs.ExceptionRefinementStep
import Lax457868Proofs.ExceptionPhaseSource
import Lax457868Proofs.ReusedOriginal.Construction.ActiveBookkeeping
import Mathlib.Tactic

/-! Fixed-source suffix for accepting one initial representative attempt and
restoring the original sample prefix for the second phase. -/

namespace Lax457868Proofs.InitialAttemptAcceptance

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax11Proofs.CC
open Lax457868Proofs.BatchedDistances
open Lax457868Proofs.ExceptionCollection
open Lax457868Proofs.SamplePacking
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ReusedOriginal.Construction.NearSweepMath
open Lax457868Proofs.ReusedOriginal.Construction.NearCheckSource
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.ReusedOriginal.Construction.NearCounterCorrectness
open Lax457868Proofs.ReusedOriginal.Construction.ActiveBookkeeping
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.ExceptionPhaseSource
open scoped symmDiff

noncomputable section

/-- A bound comparison writes the acceptance bit without modifying the
computed exception count. -/
def decideAttemptAcceptance : Com :=
  .ite (.lt (.var "exceptionCap") (.var "exceptionCount"))
    (.assign "attemptAccepted" (.lit 0))
    (.assign "attemptAccepted" (.lit 1))

lemma decideAttemptAcceptance_run
    {B cap count : ℕ} {σ : Env}
    (hcap : σ.vars "exceptionCap" = cap)
    (hcount : σ.vars "exceptionCount" = count)
    (hcapB : cap < B) (hcountB : count < B) (honeB : 1 < B) :
    ∃ σ', Run B decideAttemptAcceptance σ σ' 8 ∧
      σ'.vars "attemptAccepted" = (if count ≤ cap then 1 else 0) ∧
      (∀ a, σ'.arrs a = σ.arrs a) ∧
      (∀ v, v ≠ "attemptAccepted" → σ'.vars v = σ.vars v) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  have hcapEval : (Expr.var "exceptionCap").evalB B σ = some cap := by
    rw [evalB_var_iff]
    exact ⟨hcap.symm, by rw [hcap]; exact hcapB⟩
  have hcountEval : (Expr.var "exceptionCount").evalB B σ = some count := by
    rw [evalB_var_iff]
    exact ⟨hcount.symm, by rw [hcount]; exact hcountB⟩
  by_cases hfail : cap < count
  · let σ' := σ.setVar "attemptAccepted" 0
    have hcond : (Cond.lt (.var "exceptionCap") (.var "exceptionCount")).evalB B σ =
        some true := by
      simpa [hfail] using evalB_condLt hcapEval hcountEval
    have rassign : Run B (.assign "attemptAccepted" (.lit 0)) σ σ' 2 := by
      simpa [σ'] using (Run.assign (evalB_lit (by omega : 0 < B)))
    have hrun : Run B decideAttemptAcceptance σ σ' 8 := by
      have h := Run.ite_true
        (d := .assign "attemptAccepted" (.lit 1)) hcond rassign
      simpa [decideAttemptAcceptance, Cond.size, Expr.size] using
        h.mono (by norm_num [Cond.size, Expr.size])
    refine ⟨σ', hrun, ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ', show ¬ count ≤ cap by omega]
    · intro a; rfl
    · intro v hv; simp [σ', hv]
    · rfl
    · rfl

  · let σ' := σ.setVar "attemptAccepted" 1
    have hcond : (Cond.lt (.var "exceptionCap") (.var "exceptionCount")).evalB B σ =
        some false := by
      simpa [hfail] using evalB_condLt hcapEval hcountEval
    have rassign : Run B (.assign "attemptAccepted" (.lit 1)) σ σ' 2 := by
      simpa [σ'] using (Run.assign (evalB_lit honeB))
    have hrun : Run B decideAttemptAcceptance σ σ' 8 := by
      have h := Run.ite_false
        (c := .assign "attemptAccepted" (.lit 0)) hcond rassign
      simpa [decideAttemptAcceptance, Cond.size, Expr.size] using
        h.mono (by norm_num [Cond.size, Expr.size])
    refine ⟨σ', hrun, ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ', show count ≤ cap by omega]
    · intro a; rfl
    · intro v hv; simp [σ', hv]
    · rfl
    · rfl

/-- The exception set computed by the batched CSR counters at the supplied
runtime threshold. -/
def attemptExceptions (n u : ℕ) (x : List ℕ)
    (A C : Finset ℕ) (rep : ℕ → ℕ) : Finset ℕ :=
  exceptionSet n u (setFlag C) rep
    (degreePrefix (target x) (offset x) (setFlag A) (setFlag C) n)
    (commonPrefix (target x) (offset x) (setFlag A) (setFlag C) rep n)

/-- One actual attempt: compute all distances, collect and pack exceptions,
write its acceptance bit, then restore the original sample prefix in `ord`. -/
def initialAttemptAcceptance : Com :=
  seqs [batchedDistanceSweep, collectAndPackExceptions,
    decideAttemptAcceptance, packMarkedSamples]

lemma initialAttemptAcceptance_run
    {B n targetCap u cap : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A C W : Finset ℕ} {rep degree inter stamp neighbors ord exceptionFlags exceptionList : ℕ → ℕ}
    {σ : Env}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (_hA : A ⊆ Finset.range n) (_hC : C ⊆ Finset.range n)
    (hW : W ⊆ Finset.range n) (_hWA : W ⊆ A)
    (hrepN : ∀ v ∈ C, rep v < n)
    (hrepC : ∀ v ∈ C, rep v ∈ C)
    (hn : σ.vars "n" = n)
    (hnearBound : σ.vars "nearBound" = u)
    (hcap : σ.vars "exceptionCap" = cap)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactiveA : σ.arrs "activeA" = arrOf n (setFlag A))
    (hactiveB : σ.arrs "activeB" = arrOf n (setFlag C))
    (hrep : σ.arrs "repB" = arrOf n rep)
    (hdegree : σ.arrs "degree" = arrOf n degree)
    (hinter : σ.arrs "inter" = arrOf n inter)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hneighbors : σ.arrs "neighbors" = arrOf n neighbors)
    (hsampleFlags : σ.arrs "sampleFlags" = arrOf n (setFlag W))
    (hord : σ.arrs "ord" = arrOf n ord)
    (hexceptionFlags : σ.arrs "exceptionFlags" = arrOf n exceptionFlags)
    (hexceptionList : σ.arrs "exceptionList" = arrOf n exceptionList)
    (hnB : 2 * n + 1 < B) (htargetCapB : targetCap < B)
    (huB : u < B) (hcapB : cap < B) :
    ∃ σ' packedExceptions packedSample,
      Run B initialAttemptAcceptance σ σ'
        (300 * (n + targetCap + 1) + (94 * n + 15) + 8 + (20 * n + 9)) ∧
      σ'.arrs "exceptionFlags" = arrOf n
        (exceptionValue u (setFlag C) rep
          (degreePrefix (target x) (offset x) (setFlag A) (setFlag C) n)
          (commonPrefix (target x) (offset x) (setFlag A) (setFlag C) rep n)) ∧
      σ'.arrs "exceptionList" = arrOf n packedExceptions ∧
      PrefixEnumerates (σ'.vars "exceptionCount") packedExceptions
        (attemptExceptions n u x A C rep) ∧
      σ'.vars "exceptionCount" = (attemptExceptions n u x A C rep).card ∧
      σ'.vars "attemptAccepted" =
        (if (attemptExceptions n u x A C rep).card ≤ cap then 1 else 0) ∧
      σ'.arrs "sampleFlags" = arrOf n (setFlag W) ∧
      σ'.arrs "ord" = arrOf n packedSample ∧
      PrefixEnumerates (σ'.vars "sampleCount") packedSample W ∧
      σ'.vars "sampleCount" = W.card ∧
      (∀ b (hb : b < n) (hCb : b ∈ C),
        b ∈ attemptExceptions n u x A C rep ↔
          u < ((G.neighborSet ⟨b, hb⟩ ∩
              (activeFinset (n := n) (setFlag A) : Set (Fin n))) ∆
            (G.neighborSet ⟨rep b, hrepN b hCb⟩ ∩
              (activeFinset (n := n) (setFlag A) : Set (Fin n)))).ncard) ∧
      σ'.arrs "repB" = arrOf n rep ∧
      σ'.arrs "activeA" = arrOf n (setFlag A) ∧
      σ'.arrs "activeB" = arrOf n (setFlag C) ∧
      σ'.arrs "off" = arrOf (n + 1) (offset x) ∧
      σ'.arrs "tgt" = arrOf targetCap (target x) ∧
      σ'.vars "nearBound" = u ∧
      σ'.vars "exceptionCap" = cap ∧
      σ'.vars "n" = n ∧
      (∀ a, a ∉ batchedDistanceSweep.warrs →
        a ∉ collectAndPackExceptions.warrs → a ≠ "ord" →
        σ'.arrs a = σ.arrs a) ∧
      (∀ v, v ∉ batchedDistanceSweep.wvars →
        v ∉ collectAndPackExceptions.wvars →
        v ≠ "attemptAccepted" → v ≠ "sampleCount" →
        v ≠ "sampleCursor" → σ'.vars v = σ.vars v) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let d := degreePrefix (target x) (offset x) (setFlag A) (setFlag C) n
  let i := commonPrefix (target x) (offset x) (setFlag A) (setFlag C) rep n
  let E := attemptExceptions n u x A C rep
  have hn1B : n + 1 < B := by omega
  have hnltB : n < B := by omega
  have honeB : 1 < B := by omega
  have hactiveAB : ∀ v < n, setFlag A v < B := by
    intro v hv
    by_cases hAv : v ∈ A <;> simp [setFlag, hAv] <;> omega
  have hactiveBB : ∀ v < n, setFlag C v < B := by
    intro v hv
    by_cases hCv : v ∈ C <;> simp [setFlag, hCv] <;> omega
  have hrepN' : ∀ v < n, setFlag C v = 1 → rep v < n := by
    intro v hv hCv
    exact hrepN v (by simpa [setFlag] using hCv)
  have hrepActive : ∀ v < n, setFlag C v = 1 →
      setFlag C (rep v) = 1 := by
    intro v hv hCv
    have hvC : v ∈ C := by simpa [setFlag] using hCv
    simp [setFlag, hrepC v hvC]
  obtain ⟨σ₁, rsweep, hdegree₁, hinter₁, _hoff₁, _htarget₁,
    _hactiveA₁, hactiveB₁, hrep₁, hn₁, _hinp₁, _hout₁, hdist⟩ :=
    batchedDistanceSweep_run hx htargetCap
      (by intro v hv; rfl) (by intro j hj; rfl)
      hn hoff htarget hactiveA hactiveB hrep hdegree hinter hstamp
      hneighbors hactiveAB hactiveBB hrepN' hrepActive hn1B htargetCapB
  have hnearBound₁ : σ₁.vars "nearBound" = u :=
    (rsweep.frame_var "nearBound" (by decide)).trans hnearBound
  have hcap₁ : σ₁.vars "exceptionCap" = cap :=
    (rsweep.frame_var "exceptionCap" (by decide)).trans hcap
  have hexceptionFlags₁ : σ₁.arrs "exceptionFlags" =
      arrOf n exceptionFlags :=
    (rsweep.frame_arr "exceptionFlags" (by decide)).trans hexceptionFlags
  have hexceptionList₁ : σ₁.arrs "exceptionList" =
      arrOf n exceptionList :=
    (rsweep.frame_arr "exceptionList" (by decide)).trans hexceptionList
  obtain ⟨σ₂, packedExceptions, rcollect, hflags₂, hlist₂,
    henum₂, hcount₂, _hcursor₂, _hb₂, _hactiveB₂, _hrep₂,
    _hdegree₂, _hinter₂, hn₂, _hnearBound₂, _hinp₂, _hout₂⟩ :=
    collectAndPackExceptions_run hn₁ hnearBound₁ hactiveB₁ hrep₁
      hdegree₁ hinter₁ hexceptionFlags₁ hexceptionList₁
      hnB huB hactiveBB hrepN'
      (by intro v hv; exact degreePrefix_le _ _ _ _ n v)
      (by intro v hv; exact commonPrefix_le _ _ _ _ _ n v)
  have hEcardB : E.card < B := by
    have hsub : E ⊆ Finset.range n := by
      intro v hv
      exact (Finset.mem_filter.mp hv).1
    have hle := Finset.card_le_card hsub
    simpa using lt_of_le_of_lt (by simpa using hle) hnltB
  have hcap₂ : σ₂.vars "exceptionCap" = cap :=
    (rcollect.frame_var "exceptionCap" (by decide)).trans hcap₁
  obtain ⟨σ₃, raccept, haccepted₃, hframeArr₃, hframeVar₃,
    _hinp₃, _hout₃⟩ :=
    decideAttemptAcceptance_run hcap₂ hcount₂ hcapB hEcardB honeB
  have hsampleFlags₂ : σ₂.arrs "sampleFlags" =
      arrOf n (setFlag W) := by
    rw [rcollect.frame_arr "sampleFlags" (by decide),
      rsweep.frame_arr "sampleFlags" (by decide)]
    exact hsampleFlags
  have hord₂ : σ₂.arrs "ord" = arrOf n ord := by
    rw [rcollect.frame_arr "ord" (by decide),
      rsweep.frame_arr "ord" (by decide)]
    exact hord
  have hflags₃ : σ₃.arrs "sampleFlags" = arrOf n (setFlag W) := by
    rw [hframeArr₃ "sampleFlags"]
    exact hsampleFlags₂
  have hord₃ : σ₃.arrs "ord" = arrOf n ord := by
    rw [hframeArr₃ "ord"]
    exact hord₂
  have hn₃ : σ₃.vars "n" = n := by
    rw [hframeVar₃ "n" (by decide)]
    exact hn₂
  have hflags01 : ∀ v < n, setFlag W v ≤ 1 := by
    intro v hv
    by_cases hWv : v ∈ W <;> simp [setFlag, hWv]
  obtain ⟨σ₄, packedSample, rpack, hsampleFlags₄, hord₄,
    hsampleEnum₄, hsampleCount₄, _hsampleCursor₄,
    hframeArr₄, hframeVar₄, _hinp₄, _hout₄⟩ :=
    packMarkedSamples_run hn₃ hflags₃ hord₃ hflags01 hnltB honeB
  have hflaggedW : flaggedVertices n (setFlag W) = W := by
    ext v
    rw [show v ∈ flaggedVertices n (setFlag W) ↔
      v < n ∧ setFlag W v = 1 from mem_activeVertices]
    constructor
    · intro hv
      simpa [setFlag] using hv.2
    · intro hv
      exact ⟨Finset.mem_range.mp (hW hv), by simp [setFlag, hv]⟩
  have hrun : Run B initialAttemptAcceptance σ σ₄
      (300 * (n + targetCap + 1) + (94 * n + 15) + 8 + (20 * n + 9)) := by
    have hseq := rsweep.seq (rcollect.seq (raccept.seq rpack))
    simpa [initialAttemptAcceptance, seqs] using hseq.mono (by omega)
  refine ⟨σ₄, packedExceptions, packedSample, hrun, ?_, ?_, ?_, ?_,
    ?_, hsampleFlags₄, hord₄, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hframeArr₄ "exceptionFlags" (by decide),
      hframeArr₃ "exceptionFlags"]
    exact hflags₂
  · rw [hframeArr₄ "exceptionList" (by decide),
      hframeArr₃ "exceptionList"]
    exact hlist₂
  · rw [hframeVar₄ "exceptionCount" (by decide) (by decide),
      hframeVar₃ "exceptionCount" (by decide)]
    exact henum₂
  · rw [hframeVar₄ "exceptionCount" (by decide) (by decide),
      hframeVar₃ "exceptionCount" (by decide)]
    exact hcount₂
  · rw [hframeVar₄ "attemptAccepted" (by decide) (by decide)]
    exact haccepted₃
  · rwa [hflaggedW] at hsampleEnum₄
  · rwa [hflaggedW] at hsampleCount₄
  · intro b hb hCb
    have hmem : b ∈ E ↔ u < nearDistance d i rep b := by
      simp [E, attemptExceptions, exceptionSet, hb, setFlag, hCb, d, i]
    rw [hmem]
    have hd := hdist b hb (by simp [setFlag, hCb])
    change nearDistance d i rep b = _ at hd
    rw [hd]
  · exact (hrun.frame_arr "repB" (by decide)).trans hrep
  · exact (hrun.frame_arr "activeA" (by decide)).trans hactiveA
  · exact (hrun.frame_arr "activeB" (by decide)).trans hactiveB
  · exact (hrun.frame_arr "off" (by decide)).trans hoff
  · exact (hrun.frame_arr "tgt" (by decide)).trans htarget
  · exact (hrun.frame_var "nearBound" (by decide)).trans hnearBound
  · exact (hrun.frame_var "exceptionCap" (by decide)).trans hcap
  · exact (hrun.frame_var "n" (by decide)).trans hn
  · intro a hsweep hcollect hord
    rw [hframeArr₄ a hord, hframeArr₃ a,
      rcollect.frame_arr a hcollect, rsweep.frame_arr a hsweep]
  · intro v hsweep hcollect haccept hcount hcursor
    rw [hframeVar₄ v hcount hcursor, hframeVar₃ v haccept,
      rcollect.frame_var v hcollect, rsweep.frame_var v hsweep]
  · exact hrun.frame_inp (by decide)
  · exact hrun.out_eq (by decide)

lemma restrictedNeighborhood_finset_bridge
    {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset ℕ)
    (b : ℕ) (hb : b < n) :
    G.neighborSet ⟨b, hb⟩ ∩
      (activeFinset (n := n) (setFlag A) : Set (Fin n)) =
      finSetAsSet (numericNeighborhood G b ∩ A) := by
  ext v
  have hnear : v.val ∈ numericNeighborhood G b ↔
      G.Adj ⟨b, hb⟩ v := by
    have hvN : v.val < n := v.isLt
    rw [show v.val ∈ numericNeighborhood G b ↔ Adjn G v.val b by
      simp [numericNeighborhood, hvN]]
    constructor
    · rintro ⟨_, _, hadj⟩
      simpa using (G.adj_comm _ _).mp hadj
    · intro hadj
      exact ⟨v.isLt, hb, by simpa using (G.adj_comm _ _).mp hadj⟩
  simp [finSetAsSet, setFlag, hnear, G.adj_comm]

/-- Transport the batched counter distance to the numeric restricted
neighborhood disagreement used by the deterministic sampler. -/
lemma numeric_disagreement_eq_sweep_distance
    {n targetCap : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (A C : Finset ℕ) (rep : ℕ → ℕ)
    (b : ℕ) (hb : b < n) (hCb : b ∈ C)
    (hrN : rep b < n) (hrC : rep b ∈ C) :
    nearDistance
      (degreePrefix (target x) (offset x) (setFlag A) (setFlag C) n)
      (commonPrefix (target x) (offset x) (setFlag A) (setFlag C) rep n)
      rep b =
    disagreement (fun v => numericNeighborhood G v ∩ A) b (rep b) := by
  classical
  let X := numericNeighborhood G b ∩ A
  let Y := numericNeighborhood G (rep b) ∩ A
  have hdist := nearDistance_eq_neighborhood_symmDiff
    (target := target x) (off := offset x) (activeA := setFlag A)
    (activeB := setFlag C) (rep := rep) hx htargetCap
    (by intro v hv; rfl) (by intro j hj; rfl)
    hb hrN (by simp [setFlag, hCb]) (by simp [setFlag, hrC])
  rw [restrictedNeighborhood_finset_bridge G A b hb,
    restrictedNeighborhood_finset_bridge G A (rep b) hrN] at hdist
  have hset : (finSetAsSet (n := n) X) ∆ (finSetAsSet Y) =
      finSetAsSet (X ∆ Y) := by
    ext v
    simp [finSetAsSet, Finset.symmDiff_def, Set.symmDiff_def]
  rw [hset] at hdist
  have hXrange : X ∆ Y ⊆ Finset.range n := by
    rw [Finset.symmDiff_def]
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_filter.mp
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1).1
    · exact (Finset.mem_filter.mp
        (Finset.mem_inter.mp (Finset.mem_sdiff.mp hv).1).1).1
  rw [finSetAsSet_ncard (fun v hv => Finset.mem_range.mp (hXrange hv))] at hdist
  simpa [X, Y, disagreement, Finset.symmDiff_def] using hdist

/-- The machine threshold `k / 3` is exactly the strict threshold in the
deterministic initial-choice exception predicate. -/
lemma div_three_lt_iff (k d : ℕ) : k / 3 < d ↔ k < 3 * d := by
  omega

lemma attemptExceptions_div_three_eq
    {n targetCap k : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (A C : Finset ℕ) (hC : C ⊆ Finset.range n)
    (rep : ℕ → ℕ)
    (hrepN : ∀ b ∈ C, rep b < n)
    (hrepC : ∀ b ∈ C, rep b ∈ C) :
    attemptExceptions n (k / 3) x A C rep =
      C.filter (fun b => k < 3 *
        disagreement (fun v => numericNeighborhood G v ∩ A) b (rep b)) := by
  ext b
  by_cases hbC : b ∈ C
  · have hbN : b < n := Finset.mem_range.mp (hC hbC)
    have hdist := numeric_disagreement_eq_sweep_distance hx htargetCap
      A C rep b hbN hbC (hrepN b hbC) (hrepC b hbC)
    simp [attemptExceptions, exceptionSet, hbN, setFlag, hbC,
      hdist, div_three_lt_iff]
  · simp [attemptExceptions, exceptionSet, setFlag, hbC]

end

end Lax457868Proofs.InitialAttemptAcceptance
