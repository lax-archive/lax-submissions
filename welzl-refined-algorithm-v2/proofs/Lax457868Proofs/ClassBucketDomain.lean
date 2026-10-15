import Lax457868Proofs.EnumeratedDraws
import Lax457868Proofs.SamplerInitialProbability
import Lax457868Proofs.ReusedOriginal.Construction.RadixMath
import Lax457868Proofs.ReusedOriginal.Construction.MarkingMath

/-!
Pure adapters from a stable bucket-sort slice to the existing finite-domain
enumeration and trace-fibre types.  This module does not add a sampling law.
-/

namespace Lax457868Proofs.ClassBucketDomain

open Lax457868Proofs.EnumeratedDraws
open Lax457868Proofs.ReusedOriginal.Construction.RadixMath
open Lax457868Proofs.SamplerInitialExpectation
open Lax457868Proofs.SamplerInitialProbability
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath

/-- The finite set of input values with one specified label. -/
def labelClass (xs : List ℕ) (label : ℕ → ℕ) (d : ℕ) : Finset ℕ :=
  xs.toFinset.filter fun x => label x = d

/-- The `d`-slice of the stable bucket-sort output is a duplicate-free
enumeration of the corresponding label class. -/
lemma bucketSlice_prefixEnumerates (xs : List ℕ) (label : ℕ → ℕ)
    (q d : ℕ) (hqd : d < q) (hxs : xs.Nodup) :
    Lax457868Proofs.ReusedOriginal.Construction.MarkingMath.PrefixEnumerates
      (countDigit label xs d)
      (fun i => (bucketSort q label xs).getD (startDigit label xs d + i) 0)
      (labelClass xs label d) := by
  let ys := xs.filter fun x => label x = d
  have hyslen : ys.length = countDigit label xs d := by
    simp [ys, countDigit]
  have hysfin : ys.toFinset = labelClass xs label d := by
    ext x
    simp [ys, labelClass]
  have hentry : ∀ i < countDigit label xs d,
      (bucketSort q label xs).getD (startDigit label xs d + i) 0 =
        ys.getD i 0 := by
    intro i hi
    simpa [ys] using
      (getD_bucketSort label xs hqd hi)
  have hprefix :=
    Lax457868Proofs.ReusedOriginal.Construction.MarkingMath.PrefixEnumerates.of_list_prefix
    (xs := ys) (height := countDigit label xs d)
    (by rw [hyslen])
    (by intro i hi; exact hentry i hi)
    (hxs.filter _)
  rw [show ys.take (countDigit label xs d) = ys by
    apply List.take_of_length_le
    rw [hyslen]] at hprefix
  simpa [hysfin] using hprefix

/-- The stable slice directly yields the existing choice-domain encoding.
An empty class is allowed: `DomainEnumeration` has the unique empty-domain
equivalence and needs no representative witness. -/
noncomputable def bucketSliceDomainEnumeration (xs : List ℕ)
    (label : ℕ → ℕ) (q d : ℕ) (hqd : d < q)
    (hxs : xs.Nodup) :
    DomainEnumeration (labelClass xs label d) :=
  prefixDomainEnumeration (countDigit label xs d)
    (fun i => (bucketSort q label xs).getD (startDigit label xs d + i) 0)
    (labelClass xs label d)
    (bucketSlice_prefixEnumerates xs label q d hqd hxs)

/-- Lookup in the adapter is exactly lookup in the sorted class slice. -/
lemma bucketSliceDomainEnumeration_lookup (xs : List ℕ)
    (label : ℕ → ℕ) (q d : ℕ) (hqd : d < q)
    (hxs : xs.Nodup)
    (i : Fin (labelClass xs label d).card) :
    (bucketSliceDomainEnumeration xs label q d hqd hxs i).val =
      (bucketSort q label xs).getD (startDigit label xs d + i.val) 0 := by
  let hen := bucketSlice_prefixEnumerates xs label q d hqd hxs
  let hcard := prefixEnumerates_card _ _ _ hen
  let i' := (finEquivOfEq hcard).symm i
  have hlookup := prefixDomainEnumeration_lookup _ _ _ hen i'
  have hindex :
      (⟨i'.val, hcard ▸ i'.isLt⟩ : Fin (labelClass xs label d).card) = i := by
    apply Fin.ext
    rfl
  simpa [bucketSliceDomainEnumeration, i', hindex, finEquivOfEq] using hlookup

/-- A label class equals the corresponding trace class whenever labels encode
trace equality on the finite carrier. -/
lemma labelClass_eq_traceFiberOn (C : Finset ℕ) (label : ℕ → ℕ)
    (N : ℕ → Finset ℕ) (W : Finset ℕ) (d b₀ : ℕ)
    (hd : label b₀ = d) (hb₀ : b₀ ∈ C)
    (hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔ trace N W b = trace N W b')) :
    C.filter (fun b => label b = d) = fiberOn C N W (trace N W b₀) := by
  ext b
  simp only [Finset.mem_filter, fiberOn]
  constructor
  · rintro ⟨hb, hbd⟩
    refine ⟨hb, ?_⟩
    exact (hlabel b hb b₀ hb₀).mp (by rw [hbd, hd])
  · rintro ⟨hb, htrace⟩
    refine ⟨hb, ?_⟩
    rw [← hd]
    exact (hlabel b hb b₀ hb₀).mpr htrace

/-- For `W = drawSet A draw`, the sorted label class is the very trace fibre
used by the existing representative-choice probability model. -/
lemma labelClass_eq_traceFiber (A C : Finset ℕ) (N : ℕ → Finset ℕ)
    {r : ℕ} (draw : Fin r → A) (label : ℕ → ℕ) (d b₀ : ℕ)
    (hd : label b₀ = d) (hb₀ : b₀ ∈ C)
    (hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace N (drawSet A draw) b = trace N (drawSet A draw) b')) :
    C.filter (fun b => label b = d) =
      traceFiber A C N draw (trace N (drawSet A draw) b₀) := by
  exact labelClass_eq_traceFiberOn C label N (drawSet A draw) d b₀ hd hb₀
    hlabel

/-- The representative subtype from `SamplerInitialProbability` is carried
to the sorted label class by the same class-equality bridge. -/
noncomputable def repFiberEquivLabelClass (A C : Finset ℕ)
    (N : ℕ → Finset ℕ) {r : ℕ} (draw : Fin r → A)
    (label : ℕ → ℕ) (d b₀ : ℕ) (hd : label b₀ = d) (hb₀ : b₀ ∈ C)
    (hlabel : ∀ b ∈ C, ∀ b' ∈ C,
      (label b = label b' ↔
        trace N (drawSet A draw) b = trace N (drawSet A draw) b')) :
    RepFiber A C N draw
      ⟨trace N (drawSet A draw) b₀,
        Finset.mem_image.mpr ⟨b₀, hb₀, rfl⟩⟩ ≃
      {b // b ∈ C.filter (fun b => label b = d)} := by
  let hEq := labelClass_eq_traceFiber A C N draw label d b₀ hd hb₀ hlabel
  apply Equiv.setCongr
  ext b
  change b ∈ traceFiber A C N draw (trace N (drawSet A draw) b₀) ↔
    b ∈ C.filter (fun b => label b = d)
  rw [← hEq]

end Lax457868Proofs.ClassBucketDomain
