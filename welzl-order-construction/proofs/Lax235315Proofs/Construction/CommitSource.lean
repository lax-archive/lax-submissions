import Lax235315Proofs.Construction.WelzlStraight
import Lax235315Proofs.Construction.SourceBounds
import Lax235315Proofs.Construction.RecordRemovedSource
import Mathlib.Tactic

/-! Verification of the state-transition passes used after an accepted
reduction round. -/

namespace Lax235315Proofs.Construction.CommitSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.SourceBounds

/-- Invariant for copying the two newly selected representative sets into
the active-side arrays. -/
def AdoptInv (n : ℕ) (nextA nextB : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ activeA activeB : ℕ → ℕ,
    τ.arrs "activeA" = arrOf n activeA ∧
    τ.arrs "activeB" = arrOf n activeB ∧
    τ.arrs "nextA" = arrOf n nextA ∧
    τ.arrs "nextB" = arrOf n nextB ∧
    τ.vars "v" ≤ n ∧ τ.vars "n" = n ∧
    (∀ i < τ.vars "v", activeA i = nextA i) ∧
    (∀ i < τ.vars "v", activeB i = nextB i)

/-- The literal `adoptNext` pass replaces both active indicator arrays by
the outputs of the two verified trace partitions. -/
lemma adoptNext_run {B n : ℕ} {σ : Env}
    {activeA activeB nextA nextB : ℕ → ℕ}
    (hn : σ.vars "n" = n)
    (hactiveA : σ.arrs "activeA" = arrOf n activeA)
    (hactiveB : σ.arrs "activeB" = arrOf n activeB)
    (hnextA : σ.arrs "nextA" = arrOf n nextA)
    (hnextB : σ.arrs "nextB" = arrOf n nextB)
    (hnextAB : ∀ i < n, nextA i < B)
    (hnextBB : ∀ i < n, nextB i < B)
    (hnB : n < B) :
    ∃ σ' activeA' activeB',
      Run B adoptNext σ σ' (20 * (n + 1)) ∧
      σ'.arrs "activeA" = arrOf n activeA' ∧
      σ'.arrs "activeB" = arrOf n activeB' ∧
      (∀ i < n, activeA' i = nextA i) ∧
      (∀ i < n, activeB' i = nextB i) ∧
      σ'.vars "n" = n := by
  let body : Com := seqs [
    .store "activeA" (.var "v") (.get "nextA" (.var "v")),
    .store "activeB" (.var "v") (.get "nextB" (.var "v")),
    inc "v"]
  have hbody : Spec B
      (fun τ => AdoptInv n nextA nextB τ ∧ τ.vars "v" < n)
      body
      (fun τ τ' => AdoptInv n nextA nextB τ' ∧
        τ'.vars "v" = τ.vars "v" + 1) 14 := by
    rintro τ ⟨⟨curA, curB, hcurA, hcurB, hnA, hnB', hv, hnn,
      hfillA, hfillB⟩, hlt⟩
    have hvB : τ.vars "v" < B := hlt.trans hnB
    have hlenA : τ.vars "v" < (τ.arrs "activeA").length := by
      rw [hcurA, length_arrOf]
      exact hlt
    have hlenB : τ.vars "v" < (τ.arrs "activeB").length := by
      rw [hcurB, length_arrOf]
      exact hlt
    have hgetA : (τ.arrs "nextA")[τ.vars "v"]? = some (nextA (τ.vars "v")) := by
      rw [hnA, getElem?_arrOf nextA hlt]
    have hgetB : (τ.arrs "nextB")[τ.vars "v"]? = some (nextB (τ.vars "v")) := by
      rw [hnB', getElem?_arrOf nextB hlt]
    have hevalA : (Expr.get "nextA" (.var "v")).evalB B τ =
        some (nextA (τ.vars "v")) :=
      evalB_get (evalB_var hvB) hgetA (hnextAB _ hlt)
    have hevalB : (Expr.get "nextB" (.var "v")).evalB B τ =
        some (nextB (τ.vars "v")) :=
      evalB_get (evalB_var hvB) hgetB (hnextBB _ hlt)
    run_vcg
    refine ⟨⟨upd curA (τ.vars "v") (nextA (τ.vars "v")),
      upd curB (τ.vars "v") (nextB (τ.vars "v")), ?_, ?_, ?_, ?_,
      by simp; omega, by simp [hnn], ?_, ?_⟩, by simp⟩
    · simp [hcurA, hnA, hlt, set_arrOf_eq_upd]
    · simp [hcurB, hnB', hlt, set_arrOf_eq_upd]
    · simp [hnA]
    · simp [hnB']
    · intro i hi
      exact upd_below_succ rfl hfillA i (by simpa using hi)
    · intro i hi
      exact upd_below_succ rfl hfillB i (by simpa using hi)
    all_goals simp [hnA, hnB', hlt, hnextAB, hnextBB]
  have hshape : adoptNext =
      .seq (.assign "v" (.lit 0)) (.while (.lt (.var "v") (.var "n")) body) := by
    simp [adoptNext, body, seqs]
  rw [hshape]
  obtain ⟨σ', hrun, ⟨activeA', activeB', hactiveA', hactiveB', -, -, -,
      hnn, hfillA, hfillB⟩, hvn⟩ :=
    (Spec.forRangeZero "v" "n" (AdoptInv n nextA nextB) n 14 hnB
      (fun _ h => by
        obtain ⟨_, _, _, _, _, _, hv, _, _, _⟩ := h
        exact hv)
      (fun _ h => by
        obtain ⟨_, _, _, _, _, _, _, hnn, _, _⟩ := h
        exact hnn) hbody).run (σ := σ)
      ⟨activeA, activeB, by simp [hactiveA], by simp [hactiveB],
        by simp [hnextA], by simp [hnextB], by simp, by simp [hn],
        by intro i hi; simp at hi, by intro i hi; simp at hi⟩
  refine ⟨σ', activeA', activeB', hrun.mono (by omega), hactiveA',
    hactiveB', ?_, ?_, hnn⟩
  · intro i hi
    apply hfillA i
    simpa [hvn] using hi
  · intro i hi
    apply hfillB i
    simpa [hvn] using hi

def commitTail : Com := seqs [adoptNext,
  .store "roundEnd" (.var "round") (.var "removedCount"),
  .assign "acount" (.var "nextACount"), inc "round"]

lemma commitReduction_eq : commitReduction = .seq recordRemoved commitTail := rfl

lemma commitTail_run {B n round : ℕ} {σ : Env} {a b nextA nextB : ℕ → ℕ}
    (ha : σ.arrs "activeA" = arrOf n a)
    (hb : σ.arrs "activeB" = arrOf n b)
    (hna : σ.arrs "nextA" = arrOf n nextA)
    (hnb : σ.arrs "nextB" = arrOf n nextB)
    (hn : σ.vars "n" = n) (hnB : n < B)
    (hround : σ.vars "round" = round)
    (hrange : round < (σ.arrs "roundEnd").length)
    (hrB : round + 1 < B) (hbounded : ValuesBounded B σ) :
    ∃ σ', Run B commitTail σ σ' (20 * (n + 1) + 9) ∧
      σ'.arrs "activeA" = arrOf n nextA ∧
      σ'.arrs "activeB" = arrOf n nextB ∧
      σ'.arrs "roundEnd" = (σ.arrs "roundEnd").set round (σ.vars "removedCount") ∧
      σ'.vars "round" = round + 1 ∧ σ'.vars "acount" = σ.vars "nextACount" ∧
      σ'.arrs "removed" = σ.arrs "removed" ∧
      σ'.arrs "removedRep" = σ.arrs "removedRep" ∧
      σ'.arrs "roundStart" = σ.arrs "roundStart" ∧
      σ'.vars "removedCount" = σ.vars "removedCount" := by
  have hnextBounds (name : String) (f : ℕ → ℕ)
      (hf : σ.arrs name = arrOf n f) : ∀ i < n, f i < B := by
    intro i hi
    apply hbounded.arrays name
    rw [hf]
    exact List.mem_of_getElem? (getElem?_arrOf f hi)
  obtain ⟨τ, a', b', hr, ha', hb', hfa, hfb, _⟩ := adoptNext_run hn ha hb hna hnb
    (hnextBounds _ _ hna) (hnextBounds _ _ hnb) hnB
  have hτa : τ.arrs "activeA" = arrOf n nextA := ha'.trans (arrOf_congr hfa)
  have hτb : τ.arrs "activeB" = arrOf n nextB := hb'.trans (arrOf_congr hfb)
  have htbound := run_preserves hr hbounded
  have htround : τ.vars "round" = round :=
    (hr.frame_var "round" (by decide)).trans hround
  have htcount : τ.vars "removedCount" = σ.vars "removedCount" :=
    hr.frame_var "removedCount" (by decide)
  have htnext : τ.vars "nextACount" = σ.vars "nextACount" :=
    hr.frame_var "nextACount" (by decide)
  have htend := hr.frame_arr "roundEnd" (by decide)
  let τ₁ := τ.setArr "roundEnd" round (σ.vars "removedCount")
  let τ₂ := τ₁.setVar "acount" (σ.vars "nextACount")
  let τ₃ := τ₂.setVar "round" (round + 1)
  have r₁ : Run B (.store "roundEnd" (.var "round") (.var "removedCount"))
      τ τ₁ 3 := by
    apply Run.store
    · simpa [htround] using evalB_var (htbound.vars "round")
    · simpa [htcount] using evalB_var (htbound.vars "removedCount")
    · simpa [htend] using hrange
  have r₂ : Run B (.assign "acount" (.var "nextACount")) τ₁ τ₂ 2 := by
    apply Run.assign
    simpa [τ₁, htnext] using evalB_var (htbound.vars "nextACount")
  have r₃ : Run B (inc "round") τ₂ τ₃ 4 := by
    apply Run.assign
    apply evalB_bin
    · simpa [τ₂, τ₁, htround] using evalB_var (htbound.vars "round")
    · exact evalB_lit (by omega)
    · exact hrB
  have rrun : Run B commitTail σ τ₃ (20 * (n + 1) + 9) := by
    simpa [commitTail, seqs, Nat.add_assoc] using hr.seq (r₁.seq (r₂.seq r₃))
  refine ⟨τ₃, rrun, by simp [τ₃, τ₂, τ₁, hτa],
    by simp [τ₃, τ₂, τ₁, hτb], by simp [τ₃, τ₂, τ₁, htend],
    by simp [τ₃], by simp [τ₃, τ₂], ?_, ?_, ?_, ?_⟩
  · exact rrun.frame_arr "removed" (by decide)
  · exact rrun.frame_arr "removedRep" (by decide)
  · exact rrun.frame_arr "roundStart" (by decide)
  · exact rrun.frame_var "removedCount" (by decide)

open Lax235315Proofs.Construction.RecordRemovedSource

/-- The complete literal accepted-round commit preserves old log entries,
appends exactly the removed vertices and representatives, adopts both new
active sets, and records both boundaries of the new log interval. -/
lemma commitReduction_run {B n base round : ℕ} {σ : Env}
    {activeA activeB nextA nextB rep oldRemoved oldRep : ℕ → ℕ}
    (hn : σ.vars "n" = n) (hbase : σ.vars "removedCount" = base)
    (hround : σ.vars "round" = round)
    (ha : σ.arrs "activeA" = arrOf n activeA)
    (hb : σ.arrs "activeB" = arrOf n activeB)
    (hna : σ.arrs "nextA" = arrOf n nextA)
    (hnb : σ.arrs "nextB" = arrOf n nextB)
    (hrep : σ.arrs "repA" = arrOf n rep)
    (hrem : σ.arrs "removed" = arrOf n oldRemoved)
    (hremRep : σ.arrs "removedRep" = arrOf n oldRep)
    (hstartRange : round < (σ.arrs "roundStart").length)
    (hendRange : round < (σ.arrs "roundEnd").length)
    (hnB : n < B) (hrB : round + 1 < B)
    (hbounded : ValuesBounded B σ)
    (hcapacity : base + (removedList activeA nextA 0 n).length ≤ n) :
    ∃ σ' rem remRep, Run B commitReduction σ σ' (80 * (n + 1)) ∧
      σ'.arrs "activeA" = arrOf n nextA ∧
      σ'.arrs "activeB" = arrOf n nextB ∧
      σ'.vars "round" = round + 1 ∧
      σ'.vars "acount" = σ.vars "nextACount" ∧
      σ'.vars "removedCount" = base + (removedList activeA nextA 0 n).length ∧
      σ'.arrs "roundStart" = (σ.arrs "roundStart").set round base ∧
      σ'.arrs "roundEnd" = (σ.arrs "roundEnd").set round
        (base + (removedList activeA nextA 0 n).length) ∧
      σ'.arrs "removed" = arrOf n rem ∧ σ'.arrs "removedRep" = arrOf n remRep ∧
      (∀ j < base, rem j = oldRemoved j) ∧
      (∀ j < (removedList activeA nextA 0 n).length,
        rem (base + j) = (removedList activeA nextA 0 n).getD j 0) ∧
      (∀ j < base, remRep j = oldRep j) ∧
      (∀ j < (removedList activeA nextA 0 n).length,
        remRep (base + j) = (removedRepList activeA nextA rep 0 n).getD j 0) := by
  have arrBound (name : String) (f : ℕ → ℕ)
      (hf : σ.arrs name = arrOf n f) : ∀ i < n, f i < B := by
    intro i hi
    apply hbounded.arrays name
    rw [hf]
    exact List.mem_of_getElem? (getElem?_arrOf f hi)
  obtain ⟨τ, rem, remRep, starts, rrec, hcount, _, htn, htr,
    htrem, htrep, htstart, hstarts, hprefix, hsuffix, hprefixRep, hsuffixRep⟩ :=
    recordRemoved_run hn hround hbase ha hna hrep hrem hremRep rfl hstartRange
      hnB (by omega) (by rw [← hbase]; exact hbounded.vars _) (arrBound _ _ ha)
      (arrBound _ _ hna) (arrBound _ _ hrep) hcapacity
  have hta : τ.arrs "activeA" = arrOf n activeA :=
    (rrec.frame_arr "activeA" (by decide)).trans ha
  have htb : τ.arrs "activeB" = arrOf n activeB :=
    (rrec.frame_arr "activeB" (by decide)).trans hb
  have htna : τ.arrs "nextA" = arrOf n nextA :=
    (rrec.frame_arr "nextA" (by decide)).trans hna
  have htnb : τ.arrs "nextB" = arrOf n nextB :=
    (rrec.frame_arr "nextB" (by decide)).trans hnb
  have htend := rrec.frame_arr "roundEnd" (by decide)
  have htnext := rrec.frame_var "nextACount" (by decide)
  obtain ⟨σ', rtail, ha', hb', hend', hround', hac', hrem', hrep', hstart', hcount'⟩ :=
    commitTail_run hta htb htna htnb htn hnB htr
      (by simpa [htend] using hendRange) hrB (run_preserves rrec hbounded)
  refine ⟨σ', rem, remRep, ?_, ha', hb', hround', hac'.trans htnext,
    hcount'.trans hcount, hstart'.trans (htstart.trans hstarts), ?_,
    hrem'.trans htrem, hrep'.trans htrep, hprefix, hsuffix, hprefixRep, hsuffixRep⟩
  · rw [commitReduction_eq]
    exact (rrec.seq rtail).mono (by omega)
  · simpa [htend, hcount] using hend'

end Lax235315Proofs.Construction.CommitSource
