import Lax457868Proofs.ClassBucketDomain
import Lax457868Proofs.ClassRepresentativeMap
import Lax457868Proofs.ReusedOriginal.Construction.RadixPass

/-! A source-level adapter that first orders the existing vertices by their
class labels, then invokes the existing class representative chooser and map.
The source program is fixed; the labels and vertex list are only its input. -/

namespace Lax457868Proofs.GroupedClassRepresentatives

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.ClassRepresentativeMap
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.ClassBucketDomain
open Lax457868Proofs.EnumeratedDraws
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixMath
open Lax457868Proofs.ReusedOriginal.Construction.RadixPass
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-- The source composition: stable radix grouping by `classB`, followed by
the existing representative selection and per-vertex mapping source. -/
def groupedClassRepresentatives : Com :=
  seqs [radixPass "classB", .assign "v" (.lit 0), representativeClassMap]

lemma classStart_eq_startDigit {q : ℕ} {size : ℕ → ℕ}
    {label : ℕ → ℕ} {xs : List ℕ}
    (hsizes : ∀ d < q, size d = countDigit label xs d) :
    ∀ d ≤ q, classStart size d = startDigit label xs d := by
  intro d hd
  induction d with
  | zero => rfl
  | succ d ih =>
      have hle : d ≤ q := by omega
      have hlt : d < q := by omega
      rw [classStart, ih hle, startDigit_succ, hsizes d hlt]

private lemma bucketSlice_label (xs : List ℕ) (label : ℕ → ℕ)
    {q d k : ℕ} (hqd : d < q) (hxs : xs.Nodup)
    (hklo : startDigit label xs d ≤ k)
    (hkhi : k < startDigit label xs d + countDigit label xs d) :
    ((bucketSort q label xs).getD k 0 ∈ xs ∧
      label ((bucketSort q label xs).getD k 0) = d) := by
  let j := k - startDigit label xs d
  have hj : j < countDigit label xs d := by omega
  have hkeq : k = startDigit label xs d + j := by omega
  have hen := bucketSlice_prefixEnumerates xs label q d hqd hxs
  have hcard := prefixEnumerates_card _ _ _ hen
  let i : Fin (labelClass xs label d).card :=
    ⟨j, by rw [← hcard]; exact hj⟩
  let choice := bucketSliceDomainEnumeration xs label q d hqd hxs i
  have hlookup := bucketSliceDomainEnumeration_lookup xs label q d hqd hxs i
  have hlookup' : choice.val =
      (bucketSort q label xs).getD (startDigit label xs d + j) 0 := by
    simpa [choice, i] using hlookup
  have hmem : choice.val ∈ labelClass xs label d := choice.property
  have hmem' := Finset.mem_filter.mp hmem
  rw [hkeq, ← hlookup']
  exact ⟨List.mem_toFinset.mp hmem'.1, hmem'.2⟩

/-- Group the fixed input order by class, run the existing capped
representative source, and map successful choices back to active vertices.
The class-size array carries the preceding partition's class sizes; the proof
relates those counts to the label multiplicities. -/
lemma groupedClassRepresentatives_run_bits
    {B n q Q t : ℕ} {σ : Env}
    {xs : List ℕ} {size ord label active repClass repB key0 scratch count : ℕ → ℕ}
    {bits : List Bool} {rest : List ℕ}
    (hnpos : 0 < n) (hxn : xs.length ≤ n) (hxs : xs.Nodup)
    (hvert : ∀ x ∈ xs, x < n)
    (hlabelsInXs : ∀ x ∈ xs, label x < q)
    (hsizeCount : ∀ d < q, size d = countDigit label xs d)
    (hoccupied : ∀ d < q, 0 < size d)
    (hsizeArr : σ.arrs "classSize" = arrOf n size)
    (hordArr : σ.arrs "ord" = arrOf n ord)
    (hordPrefix : ∀ i < xs.length, ord i = xs.getD i 0)
    (hcountArr : σ.arrs "count" = arrOf Q count)
    (hscratchArr : σ.arrs "scratchOrder" = arrOf n scratch)
    (hlabelArr : σ.arrs "classB" = arrOf n label)
    (hactiveArr : σ.arrs "activeB" = arrOf n active)
    (hrepClassArr : σ.arrs "repClass" = arrOf n repClass)
    (hrepBArr : σ.arrs "repB" = arrOf n repB)
    (hkey0Arr : σ.arrs "key0" = arrOf n key0)
    (hactiveInXs : ∀ w < n, active w = 1 → w ∈ xs)
    (hactiveBound : ∀ w < n, active w < B)
    (hclassCount : σ.vars "classCount" = q)
    (halen : σ.vars "alen" = xs.length)
    (hn : σ.vars "n" = n) (hQpow : σ.vars "qpow" = Q)
    (hcap : σ.vars "drawCap" = t)
    (hinput : σ.inp = bits.map Bool.toNat ++ rest)
    (hqQ : q ≤ Q) (hQB : Q < B) (hnB : n < B)
    (htB : t < B) (htwoB : 2 < B)
    (hbudget : bitBudget size t 0 q ≤ bits.length)
    (hpowB : ∀ d < q, 2 ^ Nat.clog 2 (size d) < B) :
      ∃ values used charge failed σ' ord',
      ClassTrace size t (classStart size) 0 q bits values used charge failed ∧
      Run B groupedClassRepresentatives σ σ'
        (charge + 64 * (xs.length + Q + 1) + 104 * n + 24) ∧
      σ'.arrs "classSize" = arrOf n size ∧
      σ'.arrs "ord" = arrOf n ord' ∧
      (∀ i < xs.length, ord' i = (bucketSort Q label xs).getD i 0) ∧
      σ'.arrs "classB" = arrOf n label ∧
      σ'.arrs "activeB" = arrOf n active ∧
      σ'.arrs "repClass" = arrOf n (writeClassReps ord' repClass 0 values) ∧
      σ'.vars "repIndex" = values.length ∧
      σ'.vars "repFailed" = (if failed then 1 else 0) ∧
      (failed = false ↔ σ'.vars "repIndex" = q) ∧
      values.length ≤ q ∧ used ≤ bits.length ∧
      σ'.vars "n" = n ∧ σ'.vars "qpow" = Q ∧
      σ'.vars "classCount" = q ∧ σ'.vars "drawCap" = t ∧
      σ'.inp = (bits.drop used).map Bool.toNat ++ rest ∧
      σ'.out = σ.out ∧
      (∀ a, a ∉ groupedClassRepresentatives.warrs →
        σ'.arrs a = σ.arrs a) ∧
      (failed = true → σ'.arrs "repB" = arrOf n repB ∧ σ'.vars "v" = 0) ∧
      (failed = false → ∃ mapped : ℕ → ℕ,
        σ'.arrs "repB" = arrOf n mapped ∧
        σ'.vars "v" = n ∧
        (∀ w < n, active w = 1 →
          mapped w = writeClassReps ord' repClass 0 values (label w)) ∧
        (∀ w < n, active w = 1 →
          w ∈ xs ∧ mapped w ∈ xs ∧ label (mapped w) = label w)) := by
  have hclassStart : classStart size q = startDigit label xs q :=
    classStart_eq_startDigit hsizeCount q (by omega)
  have hstart : startDigit label xs q = xs.length := by
    rw [← length_bucketSort_eq_startDigit]
    exact (bucketSort_perm hxs hlabelsInXs).length_eq
  have hclassCountLe : ∀ d ≤ q, d ≤ classStart size d := by
    intro d hd
    induction d with
    | zero => simp [classStart]
    | succ d ih =>
      have hdq : d < q := by omega
      have hs0 := hoccupied d hdq
      have hs : 1 ≤ size d := by omega
      calc
        d + 1 ≤ classStart size d + 1 := Nat.add_le_add_right
          (ih (by omega)) 1
        _ ≤ classStart size d + size d := Nat.add_le_add_left hs _
        _ = classStart size (d + 1) := by simp [classStart]
  have hqCountLe : q ≤ classStart size q := hclassCountLe q le_rfl
  have htotal : classStart size q ≤ n := by rw [hclassStart, hstart]; exact hxn
  have hqn : q ≤ n := hqCountLe.trans htotal
  have hsizePos : ∀ d < q, 0 < size d := hoccupied
  have hqB : Q < B := hQB
  have hlabelsQ : ∀ w < n, active w = 1 → label w < q := by
    intro w hw hactive
    exact hlabelsInXs w (hactiveInXs w hw hactive)
  have hkeyLabelsQ : ∀ x ∈ xs, label x < Q := by
    intro x hx
    exact (hlabelsInXs x hx).trans_le hqQ
  have hkeyNameOrd : "classB" ≠ "ord" := by decide
  have hkeyNameCount : "classB" ≠ "count" := by decide
  have hkeyNameScratch : "classB" ≠ "scratchOrder" := by decide
  obtain ⟨σ₁, ord₁, hradix, halen₁, hQ₁, hord₁, hordval₁, hlabel₁⟩ :=
    radixPass_run (keyName := "classB") (key := label) (ord := ord)
      (count := count) (scratch := scratch) (σ := σ)
      halen hQpow hordArr hordPrefix hlabelArr hcountArr
      hscratchArr hkeyNameOrd hkeyNameCount hkeyNameScratch hxn hnB hQB
      hxs hvert hkeyLabelsQ
  have hordValue₁ : ∀ j < classStart size q, ord₁ j < n := by
    intro j hj
    have hjxs : j < xs.length := by rw [hclassStart, hstart] at hj; exact hj
    rw [hordval₁ j hjxs]
    have hmem : (bucketSort Q label xs).getD j 0 ∈ xs := by
      have hsortlen : (bucketSort Q label xs).length = xs.length :=
        (bucketSort_perm hxs hkeyLabelsQ).length_eq
      have : (bucketSort Q label xs).getD j 0 ∈ bucketSort Q label xs := by
        rw [List.getD_eq_getElem _ _ (by rw [hsortlen]; exact hjxs)]
        exact List.getElem_mem (l := bucketSort Q label xs)
          (by rw [hsortlen]; exact hjxs)
      exact (mem_bucketSort.mp this).1
    exact hvert _ hmem
  have hord₂ : σ₁.arrs "ord" = arrOf n ord₁ := hord₁
  have hsize₂ : σ₁.arrs "classSize" = arrOf n size := by
    rw [hradix.frame_arr "classSize" (by
      simp [radixPass, clearArray, seqs, inc, Com.warrs])]
    exact hsizeArr
  have hlabel₂ : σ₁.arrs "classB" = arrOf n label := hlabel₁
  have hactive₂ : σ₁.arrs "activeB" = arrOf n active := by
    rw [hradix.frame_arr "activeB" (by
      simp [radixPass, clearArray, seqs, inc, Com.warrs])]
    exact hactiveArr
  have hrep₂ : σ₁.arrs "repClass" = arrOf n repClass := by
    rw [hradix.frame_arr "repClass" (by
      simp [radixPass, clearArray, seqs, inc, Com.warrs])]
    exact hrepClassArr
  have hmap₂ : σ₁.arrs "repB" = arrOf n repB := by
    rw [hradix.frame_arr "repB" (by
      simp [radixPass, clearArray, seqs, inc, Com.warrs])]
    exact hrepBArr
  have hkey₂ : σ₁.arrs "key0" = arrOf n key0 := by
    rw [hradix.frame_arr "key0" (by
      simp [radixPass, clearArray, seqs, inc, Com.warrs])]
    exact hkey0Arr
  have hactiveBound₁ : ∀ w < n, active w < B := hactiveBound
  have hinput₁ : σ₁.inp = bits.map Bool.toNat ++ rest := by
    rw [hradix.frame_inp (by decide)]
    exact hinput
  have hclassCount₁ : σ₁.vars "classCount" = q := by
    rw [hradix.frame_var "classCount" (by
      simp [radixPass, clearArray, seqs, inc, Com.wvars])]
    exact hclassCount
  have hn₁ : σ₁.vars "n" = n := by
    rw [hradix.frame_var "n" (by
      simp [radixPass, clearArray, seqs, inc, Com.wvars])]
    exact hn
  have hqpow₁ : σ₁.vars "qpow" = Q := hQ₁
  have hcap₁ : σ₁.vars "drawCap" = t := by
    rw [hradix.frame_var "drawCap" (by
      simp [radixPass, clearArray, seqs, inc, Com.wvars])]
    exact hcap
  -- The radix counting loop uses `v`; the wrapper resets it before mapping.
  let σ₁v := σ₁.setVar "v" 0
  have hvinit : Run B (.assign "v" (.lit 0)) σ₁ σ₁v 2 := by
    simpa [σ₁v] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have hvV : σ₁v.vars "v" = 0 := by simp [σ₁v]
  have hinputV : σ₁v.inp = bits.map Bool.toNat ++ rest := by
    simpa [σ₁v] using hinput₁
  have hclassCountV : σ₁v.vars "classCount" = q := by
    simpa [σ₁v] using hclassCount₁
  have hnV : σ₁v.vars "n" = n := by simpa [σ₁v] using hn₁
  have hqpowV : σ₁v.vars "qpow" = Q := by simpa [σ₁v] using hqpow₁
  have hcapV : σ₁v.vars "drawCap" = t := by simpa [σ₁v] using hcap₁
  have hsizeV : σ₁v.arrs "classSize" = arrOf n size := by
    simpa [σ₁v] using hsize₂
  have hordV : σ₁v.arrs "ord" = arrOf n ord₁ := by
    simpa [σ₁v] using hord₂
  have hrepV : σ₁v.arrs "repClass" = arrOf n repClass := by
    simpa [σ₁v] using hrep₂
  have hmapV : σ₁v.arrs "repB" = arrOf n repB := by
    simpa [σ₁v] using hmap₂
  have hkeyV : σ₁v.arrs "key0" = arrOf n key0 := by
    simpa [σ₁v] using hkey₂
  have hactiveV : σ₁v.arrs "activeB" = arrOf n active := by
    simpa [σ₁v] using hactive₂
  have hlabelV : σ₁v.arrs "classB" = arrOf n label := by
    simpa [σ₁v] using hlabel₂
  obtain ⟨values, used, charge, failed, σ₂, key', htrace, hmapRun,
    hkeyOut, hkeyFrame, hsizeOut, hordOut, hrepOut, hprefixRep, htailRep,
    hindexOut, hstopOut, hfailedOut, hcomplete, hlen, hused, hoffset,
    hnOut, hQOut, hcountOut, hcapOut, hinpOut, houtOut,
    harrFrame, hfailedMap, hsuccessMap⟩ :=
    representativeClassMap_run_bits hbudget hsizePos hpowB htotal
      hordValue₁ hsizeV hordV hrepV hkeyV hactiveV hlabelV hmapV
      hlabelsQ hactiveBound₁ hclassCountV hnV
      (by rw [hqpowV]; exact hQB) hcapV
      hvV hnpos hinputV hqn hnB htB htwoB
  have hsuccessLabel : ∀ (mapped : ℕ → ℕ), failed = false →
      (∀ w < n, active w = 1 →
      mapped w = writeClassReps ord₁ repClass 0 values (label w)) →
      ∀ w < n, active w = 1 →
        w ∈ xs ∧ mapped w ∈ xs ∧ label (mapped w) = label w := by
    intro mapped hsuccess hcorrect w hw hwa
    have hwxs : w ∈ xs := hactiveInXs w hw hwa
    have hd : label w < q := hlabelsQ w hw hwa
    have hindex : label w < values.length := by
      rw [(ClassTrace.length_status size t (classStart size) htrace).2.mp hsuccess]
      exact hd
    have hslice := ClassTrace.values_in_slices size t (classStart size)
      htrace (label w) hindex
    have hslice' := hslice
    simp only [Nat.zero_add] at hslice'
    have hlower : startDigit label xs (label w) ≤ values[label w] := by
      rw [← classStart_eq_startDigit hsizeCount (label w) (by omega)]
      exact hslice'.1
    have hupper : values[label w] < startDigit label xs (label w) +
        countDigit label xs (label w) := by
      calc
        values[label w] < classStart size (label w) + size (label w) := hslice'.2
        _ = startDigit label xs (label w) + countDigit label xs (label w) := by
          rw [classStart_eq_startDigit hsizeCount (label w) (by omega),
            hsizeCount (label w) hd]
    have hqdQ : label w < Q := (hlabelsQ w hw hwa).trans_le hqQ
    have hchosenClass := bucketSlice_label xs label hqdQ hxs hlower hupper
    have hchosen : mapped w = (bucketSort Q label xs).getD
        (values[label w]) 0 := by
      calc
        mapped w = writeClassReps ord₁ repClass 0 values (label w) :=
          hcorrect w hw hwa
        _ = ord₁ values[label w] := by
          simpa using (writeClassReps_at ord₁ repClass 0 values
            (label w) hindex)
        _ = (bucketSort Q label xs).getD (values[label w]) 0 := by
          have hslot : values[label w] < classStart size q := by
            have hsliceBound : values[label w] < classStart size (label w + 1) := by
              simpa [classStart] using hslice'.2
            exact hsliceBound.trans_le
              (classStart_mono size (by omega))
          have hslot' : values[label w] < xs.length := by
            simpa [hclassStart, hstart] using hslot
          exact hordval₁ _ hslot'
    rw [hchosen]
    exact ⟨hwxs, hchosenClass.1, hchosenClass.2⟩
  have hQfinal : σ₂.vars "qpow" = Q := hQOut.trans hqpowV
  have hclassBfinal : σ₂.arrs "classB" = arrOf n label := by
    rw [harrFrame "classB" (by decide) (by decide) (by decide)]
    exact hlabelV
  have hactiveBfinal : σ₂.arrs "activeB" = arrOf n active := by
    rw [harrFrame "activeB" (by decide) (by decide) (by decide)]
    exact hactiveV
  have houtfinal : σ₂.out = σ.out := by
    calc
      σ₂.out = σ₁v.out := houtOut
      _ = σ₁.out := by simp [σ₁v]
      _ = σ.out := hradix.out_eq (by decide)
  have hrun := hradix.seq (hvinit.seq hmapRun)
  have hraw : Run B groupedClassRepresentatives σ σ₂
      ((64 * (xs.length + Q + 1)) + (2 + (charge + 104 * n + 22))) := by
    simpa [groupedClassRepresentatives, seqs] using hrun
  have hwhole : Run B groupedClassRepresentatives σ σ₂
      (charge + 64 * (xs.length + Q + 1) + 104 * n + 24) :=
    hraw.mono (by omega)
  have harrGeneric : ∀ a, a ∉ groupedClassRepresentatives.warrs →
      σ₂.arrs a = σ.arrs a := by
    intro a ha
    exact hwhole.frame_arr a ha
  refine ⟨values, used, charge, failed, σ₂, ord₁, htrace, hwhole,
    hsizeOut, hordOut, ?_, hclassBfinal, hactiveBfinal, hrepOut,
    hindexOut, hfailedOut, hcomplete, hlen, hused, hnOut, hQfinal,
    hcountOut, hcapOut, hinpOut, houtfinal, harrGeneric, ?_, ?_⟩
  · intro i hi
    exact hordval₁ i hi
  · intro hf
    exact hfailedMap hf
  · intro hf
    rcases hsuccessMap hf with ⟨mapped, hmapped, hvn, hcorrect⟩
    exact ⟨mapped, hmapped, hvn, hcorrect, hsuccessLabel mapped hf hcorrect⟩

end Lax457868Proofs.GroupedClassRepresentatives
