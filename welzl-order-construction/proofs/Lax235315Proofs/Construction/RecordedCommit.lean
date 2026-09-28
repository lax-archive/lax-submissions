import Lax235315Proofs.Construction.StoredHistory
import Lax235315Proofs.Construction.CertificateFrontier
import Lax235315Proofs.Construction.AcceptedCommit
import Lax235315Proofs.Construction.CommitSource
import Lax235315Proofs.Construction.RemovedRestoreBridge

/-! Accepted concrete certificates extend the chronological graph history
with the deletion order and representatives actually written by the commit. -/
namespace Lax235315Proofs.Construction.RecordedCommit

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.DriverSetup
open Lax235315Proofs.Construction.AcceptedCommit
open Lax235315Proofs.Construction.CommitSource
open Lax235315Proofs.Construction.RecordRemovedSource
open Lax235315Proofs.Construction.ActiveBookkeeping
open Lax235315Proofs.Construction.CertificateFrontier
open Lax235315Proofs.Construction.StoredHistory
open Lax235315Proofs.Construction.RecordedHistory
open Lax235315Proofs.Construction.Reconstruction
open Lax235315Proofs.Construction.LinkedSource
open Lax235315Proofs.Construction.RemovedRestoreBridge
open Lax235315Proofs.Construction.PartitionResult
open Lax235315Proofs.Construction.ConcreteReconstruction
open Lax235315Proofs.Construction.RadixEight
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RepresentativeMath
open scoped symmDiff

private lemma getD_map_of_lt {α β : Type*} (f : α → β) (xs : List α)
    (i : ℕ) (d : α) (e : β) (hi : i < xs.length) :
    (xs.map f).getD i e = f (xs.getD i d) := by
  rw [List.getD_eq_getElem? xs d ⟨i, hi⟩]
  rw [List.getD_eq_getElem? (xs.map f) e ⟨i, by simpa using hi⟩]
  simp

/-- A successful source certificate commits one graph reduction and appends
that exact scan-order deletion interval to its stored mathematical history. -/
lemma CertificateSnapshot.commit_stored_run
    {B c n bound : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    {W : Finset ℕ} {σ : Env} {τ : Env} {hFront : Frontier B c n x σ}
    (hsnap : CertificateSnapshot bound G W τ hFront)
    (hstore : Stored G bound τ) (hc : 1 ≤ c) (hn : 1 < n) (hnB : n < B)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < τ.vars "acount") :
    ∃ τ', Run B commitReduction τ τ' (80 * (n + 1)) ∧
      Frontier B c n x τ' ∧
      τ'.vars "round" = τ.vars "round" + 1 ∧
      τ'.vars "acount" = τ.vars "nextACount" ∧
      Nonempty (Stored G bound τ') := by
  obtain ⟨curB, labelB, tableB, repsB, nextB, repB, R,
      curA, labelA, tableA, repsA, nextA, repA, S,
      hB, hactiveA, hactiveB, hnextA, hnextB, hrepA, hrepB,
      dataB, ⟨hA⟩, dataA, hnear⟩ := hsnap.certificate
  have hpreActiveA : σ.arrs "activeA" = arrOf n (view σ "activeA") :=
    hFront.workspace.vertex_array (by decide) (by decide) (by decide)
  have hpreActiveB : σ.arrs "activeB" = arrOf n (view σ "activeB") :=
    hFront.workspace.vertex_array (by decide) (by decide) (by decide)
  have hactiveAStates : τ.arrs "activeA" = σ.arrs "activeA" :=
    hactiveA.trans hpreActiveA.symm
  have hactiveBStates : τ.arrs "activeB" = σ.arrs "activeB" :=
    hactiveB.trans hpreActiveB.symm
  have hactiveAEq : view τ "activeA" = view σ "activeA" := by
    funext i
    simp [view, hactiveAStates]
  have hactiveBEq : view τ "activeB" = view σ "activeB" := by
    funext i
    simp [view, hactiveBStates]
  have hbitA : ∀ i < n, nextA i ≤ 1 := by
    intro i hi
    rw [← view_of_array hnextA hi]
    exact view_bits hsnap.candidate.frontier.nextABits i
  have hnewRep : ∀ i < n, view τ "activeA" i = 1 →
      nextA i = 0 → repA i < n := by
    intro i hi hactive hremoved
    let v : Fin n := ⟨i, hi⟩
    have hactivePre : view σ "activeA" i = 1 := by
      rw [hactiveAEq] at hactive
      exact hactive
    rw [← hA.representative_val v hactivePre]
    exact (hA.partition.representative v).isLt
  have hnewRepPre : ∀ i < n, view σ "activeA" i = 1 →
      nextA i = 0 → repA i < n := by
    intro i hi hactive hremoved
    apply hnewRep i hi _ hremoved
    rw [hactiveAEq]
    exact hactive
  have hReduction {small : List (Fin n)}
      (hsmall : Enumerates (finSetAsSet S) small) :
      Nonempty (Reduction G bound
        {v : Fin n | view τ "activeA" v.val = 1}
        {v : Fin n | view τ "activeB" v.val = 1}
        (finSetAsSet S) (finSetAsSet R) small
        (restoreAfter hA.partition.representative small
          (removedFinList (n := n) (view τ "activeA") nextA))) := by
    have hnear' : ∀ b ∈ ({v : Fin n | view σ "activeB" v.val = 1} : Set (Fin n)),
        ((G.neighborSet b ∩ {v : Fin n | view σ "activeA" v.val = 1}) ∆
          (G.neighborSet (hB.partition.representative b) ∩
            {v : Fin n | view σ "activeA" v.val = 1})).ncard ≤ bound := by
      intro b hb
      have hb' : view σ "activeB" b.val = 1 := by simpa using hb
      simpa [NearCounterCorrectness.activeFinset] using hnear b hb'
    have hred := ConcreteTracePartition.reduction_of_removed_log
      hB hA dataA hbitA hnear' hsmall
    simpa only [hactiveAEq, hactiveBEq] using hred
  let candidate := hsnap.candidate
  have hroundBound := candidate.frontier.shrinking.rounds_succ_le_clog hc hn
  have hlogBound := clog_le_vertices n
  have hsub : activeVertices n nextA ⊆ activeVertices n (view τ "activeA") := by
    intro v hv
    have hv' := mem_activeVertices.mp hv
    have hnext : view τ "nextA" v = 1 := by
      rw [view_of_array hnextA hv'.1]
      exact hv'.2
    have hfrom := candidate.subset (mem_activeVertices.mpr ⟨hv'.1, hnext⟩)
    exact hfrom
  have hconserve := deleted_active_conservation hbitA hsub
    (by rw [← candidate.frontier.activeCount]; exact candidate.frontier.conservation)
  have hbase : τ.vars "removedCount" = hstore.boundary (τ.vars "round") :=
    hstore.used.symm
  have hcapacity : hstore.boundary (τ.vars "round") +
      (removedList (view τ "activeA") nextA 0 n).length ≤ n := by
    have h := hconserve
    rw [hbase] at h
    omega
  have hcapacityPre : hstore.boundary (τ.vars "round") +
      (removedList (view σ "activeA") nextA 0 n).length ≤ n := by
    simpa [hactiveAEq] using hcapacity
  have hroundLt : τ.vars "round" < n := by omega
  have hrB : τ.vars "round" + 1 < B := by omega
  have arr (a : String) (h₁ : a ≠ "off") (h₂ : a ≠ "tgt")
      (h₃ : a ≠ "count") := candidate.frontier.workspace.vertex_array h₁ h₂ h₃
  have hremovedBoundArray : τ.arrs "removed" = arrOf n (view τ "removed") :=
    arr "removed" (by decide) (by decide) (by decide)
  have hrepBoundArray : τ.arrs "removedRep" = arrOf n (view τ "removedRep") :=
    arr "removedRep" (by decide) (by decide) (by decide)
  have hstartRange : τ.vars "round" < (τ.arrs "roundStart").length := by
    rw [candidate.frontier.workspace.lengths]
    change τ.vars "round" < n
    exact hroundLt
  have hendRange : τ.vars "round" < (τ.arrs "roundEnd").length := by
    rw [candidate.frontier.workspace.lengths]
    change τ.vars "round" < n
    exact hroundLt
  have hremovedBound : ∀ i < n, view τ "removed" i < n := hstore.removedBound
  have hrepBound : ∀ i < n, view τ "removedRep" i < n := hstore.representativeBound
  obtain ⟨τ₁, rem, remRep, hfull₁⟩ :=
    commitReduction_run candidate.frontier.workspace.vertices hbase rfl
      hactiveA hactiveB hnextA hnextB hrepA hremovedBoundArray hrepBoundArray
      hstartRange hendRange hnB hrB candidate.frontier.workspace.bounded hcapacityPre
  have hrun₁ : Run B commitReduction τ τ₁ (80 * (n + 1)) := hfull₁.1
  have hrunFinal : Run B commitReduction τ τ₁ (80 * (n + 1)) := hrun₁
  rcases hfull₁.2 with ⟨hactiveA₁, hactiveB₁, hround₁,
      hacount₁, hremovedCount₁, hstarts₁, hends₁, hremoved₁, hrep₁,
      hprefix₁, hsuffix₁, hprefixRep₁, hsuffixRep₁, htail₁, htailRep₁⟩
  obtain ⟨τb, remB, remRepB, hfullB⟩ :=
    commitReduction_run_logValues_lt candidate.frontier.workspace.vertices hbase rfl
      hactiveA hactiveB hnextA hnextB hrepA hremovedBoundArray hrepBoundArray
      hstartRange hendRange hnB hrB candidate.frontier.workspace.bounded hcapacityPre
      hremovedBound hrepBound hnewRepPre
  have hrunB : Run B commitReduction τ τb (80 * (n + 1)) := hfullB.1
  rcases hfullB.2 with ⟨harrRemovedB, harrRepB, hlogBound⟩
  obtain ⟨τf, hfullf⟩ :=
    candidate.commit hc hn hnB hlarge
  have hrunf : Run B commitReduction τ τf (80 * (n + 1)) := hfullf.1
  rcases hfullf.2 with ⟨hfrontier, hroundf, hacountf⟩
  obtain ⟨_, _, hbs1⟩ := hrun₁
  obtain ⟨_, _, hbsB⟩ := hrunB
  obtain ⟨_, _, hbsF⟩ := hrunf
  have hτb : τb = τ₁ := (BigStep.unique hbsB.bigStep hbs1.bigStep).1
  subst τb
  have hτf : τf = τ₁ := (BigStep.unique hbsF.bigStep hbs1.bigStep).1
  subst τf
  have hlogSlice : logSlice (view τ₁ "removed") (hstore.boundary (τ.vars "round"))
      (removedList (view σ "activeA") nextA 0 n).length =
      (removedFinList (n := n) (view σ "activeA") nextA).map Fin.val := by
    have hget : ∀ j < (removedList (view σ "activeA") nextA 0 n).length,
        view τ₁ "removed" (hstore.boundary (τ.vars "round") + j) =
          (removedList (view σ "activeA") nextA 0 n).getD j 0 := by
      intro j hj
      have hi : hstore.boundary (τ.vars "round") + j < n := by omega
      rw [view_of_array hremoved₁ hi, hsuffix₁ j hj]
    rw [logSlice_eq_of_stored_getD hget]
    exact (removedFinList_map_val (view σ "activeA") nextA).symm
  let round := τ.vars "round"
  let base := hstore.boundary round
  let dlen := (removedList (view σ "activeA") nextA 0 n).length
  let boundary' := Function.update hstore.boundary (round + 1) (base + dlen)
  let deleted := removedFinList (n := n) (view σ "activeA") nextA
  let representative := hA.partition.representative
  have hdeletedLen : deleted.length = dlen := by
    dsimp [deleted, dlen]
    rw [← List.length_map Fin.val]
    rw [removedFinList_map_val]
  have hstart : boundary' round = base := by simp [boundary', round, base]
  have hend : boundary' (round + 1) = base + dlen := by simp [boundary', round, base]
  have hcount : boundary' (round + 1) - boundary' round = dlen := by
    rw [hend, hstart]
    simp [dlen]
  have hstep : RecordedStep G bound round (hstore.A round) (hstore.C round)
      {v : Fin n | view τ₁ "activeA" v.val = 1}
      {v : Fin n | view τ₁ "activeB" v.val = 1}
      boundary' (view τ₁ "removed") (view τ₁ "removedRep") := by
    refine ⟨deleted, representative, ?_, ?_, ?_, ?_, ?_⟩
    ·
      have hlen : boundary' (round + 1) - base = dlen := by
        rw [← hstart, hcount]
      rw [hstart, hlen]
      simpa [deleted, dlen] using hlogSlice.symm
    · intro i hi
      have hi' : i < dlen := by simpa [hcount] using hi
      let zeroFin : Fin n := ⟨0, by omega⟩
      have hgetNum : (deleted.getD i zeroFin).val =
          (removedList (view σ "activeA") nextA 0 n).getD i 0 := by
        calc
          (deleted.getD i zeroFin).val =
              (deleted.map Fin.val).getD i 0 := by
            symm
            exact getD_map_of_lt Fin.val deleted i zeroFin 0 (by
              simpa [hdeletedLen] using hi')
          _ = (removedList (view σ "activeA") nextA 0 n).getD i 0 := by
            simpa [deleted] using congrArg (fun l : List ℕ => l.getD i 0)
              (removedFinList_map_val (n := n) (view σ "activeA") nextA)
      -- The parallel representative log is pointwise the concrete A-partition map.
      have hgetRemoved : view τ₁ "removed" (base + i) = (deleted.getD i zeroFin).val := by
        have hget := hsuffix₁ i hi'
        have hidx : base + i < n := by
          have hiCap := Nat.add_lt_add_left hi' base
          exact hiCap.trans_le (by simpa [base, dlen] using hcapacityPre)
        rw [view_of_array hremoved₁ hidx, hget, hgetNum]
      have hgetRep : view τ₁ "removedRep" (base + i) =
          (removedRepList (view σ "activeA") nextA repA 0 n).getD i 0 := by
        have hget := hsuffixRep₁ i hi'
        have hidx : base + i < n := by
          have hiCap := Nat.add_lt_add_left hi' base
          exact hiCap.trans_le (by simpa [base, dlen] using hcapacityPre)
        rw [view_of_array hrep₁ hidx, hget]
      rw [hstart]
      rw [hgetRemoved, numericRepresentative_val]
      rw [hgetRep]
      have hmap := removedFinList_concrete_representative_map (n := n)
        (active := view σ "activeA") (next := nextA) (repOf := repA) hA
      have hpoint : (representative (deleted.getD i zeroFin)).val =
          (removedRepList (view σ "activeA") nextA repA 0 n).getD i 0 := by
        calc
          (representative (deleted.getD i zeroFin)).val =
              (deleted.map (fun v => (representative v).val)).getD i 0 := by
            symm
            exact getD_map_of_lt (fun v => (representative v).val) deleted i zeroFin 0
              (by simpa [hdeletedLen] using hi')
          _ = (removedRepList (view σ "activeA") nextA repA 0 n).getD i 0 := by
            simpa [deleted] using congrArg (fun l : List ℕ => l.getD i 0) hmap
      exact hpoint
    · have hOld : hstore.A round = {v : Fin n | view σ "activeA" v.val = 1} := by
        simpa [hactiveAEq] using hstore.currentA
      have hNew : {v : Fin n | view τ₁ "activeA" v.val = 1} = finSetAsSet S := by
        ext v
        change view τ₁ "activeA" v.val = 1 ↔ v.val ∈ S
        rw [view_of_array hactiveA₁ v.isLt]
        exact dataA.out_mem v.val v.isLt
      rw [hOld, hNew]
      simpa [deleted] using removedFinList_enumerates hbitA dataA
    · intro v hv
      have hmem := mem_removedFinList.mp hv
      have hactive : view σ "activeA" v.val = 1 :=
        (mem_removedList.mp hmem).2.2.1
      have hrepmem := hA.partition.representative_mem v hactive
      have hS : (representative v).val ∈ S := by simpa [finSetAsSet] using hrepmem
      change view τ₁ "activeA" (representative v).val = 1
      rw [view_of_array hactiveA₁ (representative v).isLt]
      exact (dataA.out_mem (representative v).val (representative v).isLt).2 hS
    · intro small hsmall
      have hNew : {v : Fin n | view τ₁ "activeA" v.val = 1} = finSetAsSet S := by
        ext v
        change view τ₁ "activeA" v.val = 1 ↔ v.val ∈ S
        rw [view_of_array hactiveA₁ v.isLt]
        exact dataA.out_mem v.val v.isLt
      have hsmall' : Enumerates (finSetAsSet S) small := by simpa [hNew] using hsmall
      have hOldA : hstore.A round = {v : Fin n | view τ "activeA" v.val = 1} := by
        simpa using hstore.currentA
      have hOldB : hstore.C round = {v : Fin n | view τ "activeB" v.val = 1} := by
        simpa using hstore.currentC
      have hNewB : {v : Fin n | view τ₁ "activeB" v.val = 1} = finSetAsSet R := by
        ext v
        change view τ₁ "activeB" v.val = 1 ↔ v.val ∈ R
        rw [view_of_array hactiveB₁ v.isLt]
        exact dataB.out_mem v.val v.isLt
      have hred := hReduction hsmall'
      simpa [deleted, representative, hactiveAEq, hactiveBEq, hOldA, hOldB,
        hNew, hNewB] using hred
  have hremovedPrefix : ∀ i < τ.vars "removedCount",
      view τ₁ "removed" i = view τ "removed" i := by
    intro i hi
    have hi' : i < hstore.boundary round := by rw [← hbase]; exact hi
    have hlen : (τ.arrs "removed").length = n := candidate.frontier.workspace.lengths "removed"
    have hiN : i < n := lt_of_lt_of_le hi' (hstore.capacity _ le_rfl)
    rw [view_of_array hremoved₁ hiN, view_of_array hremovedBoundArray hiN,
      hprefix₁ i hi']
  have hrepPrefix : ∀ i < τ.vars "removedCount",
      view τ₁ "removedRep" i = view τ "removedRep" i := by
    intro i hi
    have hi' : i < hstore.boundary round := by rw [← hbase]; exact hi
    have hiN : i < n := lt_of_lt_of_le hi' (hstore.capacity _ le_rfl)
    rw [view_of_array hrep₁ hiN, view_of_array hrepBoundArray hiN,
      hprefixRep₁ i hi']
  have hboundary : ∀ r' ≤ round, boundary' r' = hstore.boundary r' := by
    intro r' hr'
    simp [boundary', show r' ≠ round + 1 by omega]
  have hnewBoundary : boundary' (round + 1) = τ₁.vars "removedCount" := by
    simp [boundary', base, dlen, round, hremovedCount₁]
  have hstarts : ∀ r' < τ₁.vars "round", view τ₁ "roundStart" r' = boundary' r' := by
    intro r' hr'
    rw [hround₁] at hr'
    by_cases heq : r' = round
    · subst r'
      change ((τ₁.arrs "roundStart").getD (τ.vars "round") 0) = boundary' (τ.vars "round")
      rw [hstarts₁]
      rw [List.getD_eq_getElem _ _ (by simpa [List.length_set] using hstartRange)]
      rw [List.getElem_set_self (by simpa [List.length_set] using hstartRange)]
      simpa [boundary', round, base,
        show τ.vars "round" ≠ τ.vars "round" + 1 by omega]
    · have hrOld : r' < round := by omega
      have hold := hstore.starts r' hrOld
      have hstartView : view τ₁ "roundStart" r' = view τ "roundStart" r' := by
        change (τ₁.arrs "roundStart").getD r' 0 = (τ.arrs "roundStart").getD r' 0
        rw [hstarts₁]
        simp [List.getElem?_set, show τ.vars "round" ≠ r' by omega]
      rw [hstartView, hold, hboundary r' (by omega)]
  have hends : ∀ r' < τ₁.vars "round", view τ₁ "roundEnd" r' = boundary' (r' + 1) := by
    intro r' hr'
    rw [hround₁] at hr'
    by_cases heq : r' = round
    · subst r'
      change ((τ₁.arrs "roundEnd").getD (τ.vars "round") 0) = boundary' (τ.vars "round" + 1)
      rw [hends₁]
      rw [List.getD_eq_getElem _ _ (by simpa [List.length_set] using hendRange)]
      rw [List.getElem_set_self (by simpa [List.length_set] using hendRange)]
      simp [boundary', base, dlen, round, hremovedCount₁]
    · have hrOld : r' < round := by omega
      have hold := hstore.ends r' hrOld
      have hendView : view τ₁ "roundEnd" r' = view τ "roundEnd" r' := by
        change (τ₁.arrs "roundEnd").getD r' 0 = (τ.arrs "roundEnd").getD r' 0
        rw [hends₁]
        simp [List.getElem?_set, show τ.vars "round" ≠ r' by omega]
      rw [hendView, hold, hboundary (r' + 1) (by omega)]
  have hlogBounds : ∀ i < n,
      view τ₁ "removed" i < n ∧ view τ₁ "removedRep" i < n := by
    intro i hi
    have hv := hlogBound i hi
    constructor
    · simpa [view, harrRemovedB] using hv.1
    · simpa [view, harrRepB] using hv.2
  have hstored := hstore.append hround₁ hboundary hnewBoundary
    (by rw [hremovedCount₁, ← hbase]; omega)
    (by rw [hremovedCount₁]; simpa [hactiveAEq] using hcapacity)
    hstarts hends hremovedPrefix hrepPrefix
    (fun i hi => (hlogBounds i hi).1) (fun i hi => (hlogBounds i hi).2) hstep
  exact ⟨τ₁, hrunFinal, hfrontier, hround₁, hacount₁, ⟨hstored⟩⟩

end Lax235315Proofs.Construction.RecordedCommit
