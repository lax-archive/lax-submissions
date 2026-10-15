import Lax457868Proofs.ClassRepresentativeLoop
import Lax457868Proofs.ReusedOriginal.Construction.RepresentativeSource

/-!
Choose one representative in each compact class, then fill the per-vertex
representative array using the existing source mapping loop.  A failed class
draw skips the mapping loop, retaining the old per-vertex array.
-/

namespace Lax457868Proofs.ClassRepresentativeMap

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.FairBitIndices Lax457868Proofs.FairBitRam
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.ReusedOriginal.Construction.RepresentativeSource
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-- Fixed source: the map runs only when every class draw succeeded. -/
def representativeClassMap : Com :=
  seqs [representativeClassLoop,
    .ite (.eq (.var "repFailed") (.lit 0))
      (seqs [
        .assign "v" (.lit 0),
        .while (.lt (.var "v") (.var "n"))
          (representativeMapBody "activeB" "classB" "repB")])
      .skip]

private lemma selected_in_range
    {n q t : ℕ} {size ord rep : ℕ → ℕ}
    {bits : List Bool} {values : List ℕ} {used charge : ℕ}
    (htrace : ClassTrace size t (classStart size) 0 q bits values used charge false)
    (hord : ∀ j < classStart size q, ord j < n)
    {j : ℕ} (hj : j < q) :
    writeClassReps ord rep 0 values j < n := by
  have hlength := (ClassTrace.length_status size t (classStart size) htrace).2.mp rfl
  have hj' : j < values.length := by simpa [hlength] using hj
  have hslice := ClassTrace.values_in_slices size t (classStart size) htrace j hj'
  have hupper : values[j] < classStart size q := by
    have hmono := classStart_mono size (show j + 1 ≤ q by omega)
    have hslice' : values[j] < classStart size (j + 1) := by
      simpa [classStart] using hslice.2
    exact lt_of_lt_of_le hslice' hmono
  rw [show j = 0 + j by omega, writeClassReps_at ord rep 0 values j hj']
  exact hord _ hupper

/-- The composed source uses one flat bit tape.  On success it maps every
active vertex to its selected class representative.  On failure it leaves
the old per-vertex map in place. -/
lemma representativeClassMap_run_bits
    {B n q v t : ℕ} {σ : Env}
    {size ord rep key active label oldMap : ℕ → ℕ}
    {bits : List Bool} {rest : List ℕ}
    (hbudget : bitBudget size t 0 q ≤ bits.length)
    (hpositive : ∀ d < q, 0 < size d)
    (hpowB : ∀ d < q, 2 ^ Nat.clog 2 (size d) < B)
    (htotal : classStart size q ≤ n)
    (hordValue : ∀ j < classStart size q, ord j < n)
    (hsize : σ.arrs "classSize" = arrOf n size)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hrep : σ.arrs "repClass" = arrOf n rep)
    (hkey : σ.arrs "key0" = arrOf n key)
    (hactive : σ.arrs "activeB" = arrOf n active)
    (hlabel : σ.arrs "classB" = arrOf n label)
    (holdMap : σ.arrs "repB" = arrOf n oldMap)
    (hlabels : ∀ w < n, active w = 1 → label w < q)
    (hactiveB : ∀ w < n, active w < B)
    (hcount : σ.vars "classCount" = q)
    (hn : σ.vars "n" = n) (hqpow : σ.vars "qpow" < B)
    (hcap : σ.vars "drawCap" = t)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hinp : σ.inp = bits.map Bool.toNat ++ rest)
    (hqn : q ≤ n) (hnB : n < B)
    (htB : t < B) (htwoB : 2 < B) :
    ∃ (values : List ℕ) (used charge : ℕ) (failed : Bool)
      (σ' : Env) (key' : ℕ → ℕ),
      ClassTrace size t (classStart size) 0 q bits values used charge failed ∧
      Run B representativeClassMap σ σ' (charge + 104 * n + 22) ∧
      σ'.arrs "key0" = arrOf n key' ∧
      (∀ j < n, j ≠ v → key' j = key j) ∧
      σ'.arrs "classSize" = arrOf n size ∧
      σ'.arrs "ord" = arrOf n ord ∧
      σ'.arrs "repClass" = arrOf n (writeClassReps ord rep 0 values) ∧
      (∀ j (hj : j < values.length),
        (σ'.arrs "repClass")[j]? = some (ord values[j])) ∧
      (∀ j (_hj : j < n), values.length ≤ j →
        (σ'.arrs "repClass")[j]? = some (rep j)) ∧
      σ'.vars "repIndex" = values.length ∧
      σ'.vars "repStop" = (if failed then values.length else q) ∧
      σ'.vars "repFailed" = (if failed then 1 else 0) ∧
      (failed = false ↔ σ'.vars "repIndex" = q) ∧
      values.length ≤ q ∧ used ≤ bits.length ∧
      σ'.vars "drawOffset" = classStart size values.length ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = σ.vars "qpow" ∧
      σ'.vars "classCount" = q ∧ σ'.vars "drawCap" = t ∧
      σ'.inp = (bits.drop used).map Bool.toNat ++ rest ∧
      σ'.out = σ.out ∧
      (∀ a, a ≠ "key0" → a ≠ "repClass" → a ≠ "repB" →
        σ'.arrs a = σ.arrs a) ∧
      (failed = true → σ'.arrs "repB" = arrOf n oldMap ∧ σ'.vars "v" = v) ∧
      (failed = false → ∃ mapped : ℕ → ℕ,
        σ'.arrs "repB" = arrOf n mapped ∧ σ'.vars "v" = n ∧
        ∀ w < n, active w = 1 →
          mapped w = writeClassReps ord rep 0 values (label w)) := by
  obtain ⟨values, used, charge, failed, σ₁, key', htrace, hloop,
    hkey₁, hkeyFrame, hsize₁, hord₁, hrep₁, hprefix₁, htail₁,
    hindex₁, hstop₁, hbad₁, hcomplete₁, hlen, hused,
    hoffset₁, hn₁, hqpow₁, hcount₁, hcap₁, hv₁, hinp₁,
    hout₁, harrFrame₁⟩ :=
      representativeClassLoop_run_bits hbudget hpositive hpowB htotal
        hordValue hsize hord hrep hkey hcount hn hqpow hcap hv hvn
        hinp hqn hnB htB htwoB
  have hactive₁ : σ₁.arrs "activeB" = arrOf n active :=
    (harrFrame₁ "activeB" (by decide) (by decide)).trans hactive
  have hlabel₁ : σ₁.arrs "classB" = arrOf n label :=
    (harrFrame₁ "classB" (by decide) (by decide)).trans hlabel
  have hmap₁ : σ₁.arrs "repB" = arrOf n oldMap :=
    (harrFrame₁ "repB" (by decide) (by decide)).trans holdMap
  by_cases hfailed : failed = false
  · subst failed
    have htest : (Cond.eq (.var "repFailed") (.lit 0)).evalB B σ₁ = some true := by
      simpa [hbad₁] using
        evalB_condEq (evalB_var (by simp [hbad₁]; omega : σ₁.vars "repFailed" < B))
          (evalB_lit (by omega : 0 < B))
    let σ₂ := σ₁.setVar "v" 0
    have hinit : Run B (.assign "v" (.lit 0)) σ₁ σ₂ 2 := by
      simpa [σ₂] using (Run.assign (evalB_lit (by omega : 0 < B)))
    have hmapInv : RepMapInv n q "activeB" "classB" "repB"
        active label (writeClassReps ord rep 0 values) σ₂ := by
      refine ⟨oldMap, ?_, ?_, hqn, ?_, ?_, ?_, ?_, hlabels, ?_⟩
      · simp [σ₂]
      · simp [σ₂, hn₁]
      · simpa [σ₂] using hactive₁
      · simpa [σ₂] using hlabel₁
      · simpa [σ₂] using hrep₁
      · simpa [σ₂] using hmap₁
      · intro w hw; simp [σ₂] at hw
    have hrepRange : ∀ w < n, active w = 1 →
        writeClassReps ord rep 0 values (label w) < n := by
      intro w hw haw
      exact selected_in_range htrace hordValue (hlabels w hw haw)
    obtain ⟨σ₃, mapped, hmapRun, hv₃, hmap₃, hcorrect⟩ :=
      representativeMapLoop_run hmapInv hnB (by omega) hactiveB hrepRange
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hbranch : Run B
        (.ite (.eq (.var "repFailed") (.lit 0))
          (seqs [.assign "v" (.lit 0),
            .while (.lt (.var "v") (.var "n"))
              (representativeMapBody "activeB" "classB" "repB")]) .skip)
        σ₁ σ₃ (104 * n + 10) := by
      have hseq := Run.seq hinit hmapRun
      have h := Run.ite_true (d := .skip) htest hseq
      have hraw : Run B
          (.ite (.eq (.var "repFailed") (.lit 0))
            (seqs [.assign "v" (.lit 0),
              .while (.lt (.var "v") (.var "n"))
                (representativeMapBody "activeB" "classB" "repB")]) .skip)
          σ₁ σ₃ (4 + (2 + (104 * n + 4))) := by
        simpa [seqs] using h
      exact hraw.mono (by omega)
    have hrun : Run B representativeClassMap σ σ₃ (charge + 104 * n + 22) := by
      have h := Run.seq hloop hbranch
      have hraw : Run B representativeClassMap σ σ₃
          ((charge + 12) + (104 * n + 10)) := by
        simpa [representativeClassMap, seqs] using h
      exact hraw.mono (by omega)
    refine ⟨values, used, charge, false, σ₃, key', htrace, hrun,
      ?_, hkeyFrame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlen, hused,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hmapRun.frame_arr "key0" (by decide)).trans hkey₁
    · exact (hmapRun.frame_arr "classSize" (by decide)).trans hsize₁
    · exact (hmapRun.frame_arr "ord" (by decide)).trans hord₁
    · exact (hmapRun.frame_arr "repClass" (by decide)).trans hrep₁
    · intro j hj
      rw [hmapRun.frame_arr "repClass" (by decide)]
      exact hprefix₁ j hj
    · intro j hj hout
      rw [hmapRun.frame_arr "repClass" (by decide)]
      exact htail₁ j hj hout
    · exact (hmapRun.frame_var "repIndex" (by decide)).trans hindex₁
    · exact (hmapRun.frame_var "repStop" (by decide)).trans hstop₁
    · exact (hmapRun.frame_var "repFailed" (by decide)).trans hbad₁
    · constructor
      · intro _
        exact (hmapRun.frame_var "repIndex" (by decide)).trans
          (hcomplete₁.mp rfl)
      · intro _
        rfl
    · exact (hmapRun.frame_var "drawOffset" (by decide)).trans hoffset₁
    · exact (hmapRun.frame_var "n" (by decide)).trans hn₁
    · exact (hmapRun.frame_var "qpow" (by decide)).trans hqpow₁
    · exact (hmapRun.frame_var "classCount" (by decide)).trans hcount₁
    · exact (hmapRun.frame_var "drawCap" (by decide)).trans hcap₁
    · exact (hmapRun.frame_inp (by decide)).trans hinp₁
    · exact (hmapRun.out_eq (by decide)).trans hout₁
    · intro a ha hb hc
      have hnot : a ∉
          (representativeMapBody "activeB" "classB" "repB").warrs := by
        simp [representativeMapBody, seqs, Com.warrs, inc, hc]
      exact (hmapRun.frame_arr a hnot).trans (harrFrame₁ a ha hb)
    · simp
    · intro _
      exact ⟨mapped, hmap₃, hv₃, hcorrect⟩
  · have hfailed' : failed = true := by cases failed <;> simp_all
    have htest : (Cond.eq (.var "repFailed") (.lit 0)).evalB B σ₁ = some false := by
      simpa [hbad₁, hfailed'] using
        evalB_condEq (evalB_var (by simp [hbad₁, hfailed']; omega : σ₁.vars "repFailed" < B))
          (evalB_lit (by omega : 0 < B))
    have hbranch : Run B
        (.ite (.eq (.var "repFailed") (.lit 0))
          (seqs [.assign "v" (.lit 0),
            .while (.lt (.var "v") (.var "n"))
              (representativeMapBody "activeB" "classB" "repB")]) .skip)
        σ₁ σ₁ 5 := by
      simpa using (Run.ite_false htest Run.skip)
    have hrun : Run B representativeClassMap σ σ₁ (charge + 104 * n + 22) := by
      have h := Run.seq hloop hbranch
      have hraw : Run B representativeClassMap σ σ₁ (charge + 17) := by
        simpa [representativeClassMap, seqs] using h
      exact hraw.mono (by omega)
    refine ⟨values, used, charge, failed, σ₁, key', htrace, hrun,
      hkey₁, hkeyFrame, hsize₁, hord₁, hrep₁, hprefix₁, htail₁,
      hindex₁, hstop₁, hbad₁, hcomplete₁, hlen, hused,
      hoffset₁, hn₁, hqpow₁, hcount₁, hcap₁,
      hinp₁, hout₁, ?_, ?_, ?_⟩
    · intro a ha hb hc
      exact harrFrame₁ a ha hb
    · intro _
      exact ⟨hmap₁, hv₁⟩
    · intro hf
      exact (hfailed hf).elim

end Lax457868Proofs.ClassRepresentativeMap
