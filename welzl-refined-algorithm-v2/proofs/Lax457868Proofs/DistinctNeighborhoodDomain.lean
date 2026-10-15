import Mathlib.Tactic
import Lax457868Proofs.EnumeratedDraws
import Lax457868Proofs.GraphTraceBounds
import Lax457868Proofs.VerifiedPartitionBridge
import Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource

set_option autoImplicit false

/-! The existing first partition command, run with the whole active ground
set as its tests, yields the source representatives of distinct full
neighborhoods. -/

namespace Lax457868Proofs.DistinctNeighborhoodDomain

open Lax457868Proofs.EnumeratedDraws
open Lax457868Proofs.GraphTraceBounds
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.NeighborhoodComplexity
open Lax457868Proofs.ReusedOriginal.Construction.PartitionCompleteSource
open Lax457868Proofs.ReusedOriginal.Construction.PartitionResult
open Lax457868Proofs.ReusedOriginal.Construction.RepresentativeMath
open Lax457868Proofs.ReusedOriginal.Construction.RoundPartitionSource
open Lax457868Proofs.ReusedOriginal.Construction.TracePartitions
open Lax457868Proofs.VerifiedPartitionBridge
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax808846Proofs.Imp
open Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax11.GraphEncoding

noncomputable section

/-- Input arrays and invariants for one actual source partition call.  The
occupied `ord` prefix enumerates exactly the active set `A`; no partition,
representative, or desired result is supplied as input. -/
structure DistinctNeighborhoodInput (B n targetCap sampleCount : ℕ)
    (G : SimpleGraph (Fin n)) (x : List ℕ)
    (A C : Finset (Fin n)) (Wnum : Finset ℕ) where
  σ : Env
  activeB : ℕ → ℕ
  ord : ℕ → ℕ
  classB : ℕ → ℕ
  classSize : ℕ → ℕ
  markedCount : ℕ → ℕ
  stamp : ℕ → ℕ
  marked : ℕ → ℕ
  touched : ℕ → ℕ
  split : ℕ → ℕ
  repClass : ℕ → ℕ
  repsB : ℕ → ℕ
  nextB : ℕ → ℕ
  repB : ℕ → ℕ
  hx : EncodesGraph x n G
  htargetCap : targetCap = 2 * edgeCount x
  hn : σ.vars "n" = n
  hsampleCount : σ.vars "sampleCount" = sampleCount
  hoff : σ.arrs "off" = arrOf (n + 1) (offset x)
  htarget : σ.arrs "tgt" = arrOf targetCap (target x)
  hactiveBArray : σ.arrs "activeB" = arrOf n activeB
  hord : σ.arrs "ord" = arrOf n ord
  hclassB : σ.arrs "classB" = arrOf n classB
  hclassSize : σ.arrs "classSize" = arrOf n classSize
  hmarkedCount : σ.arrs "markedCount" = arrOf n markedCount
  hstamp : σ.arrs "stamp" = arrOf n stamp
  hmarked : σ.arrs "marked" = arrOf n marked
  htouched : σ.arrs "touched" = arrOf n touched
  hsplit : σ.arrs "split" = arrOf n split
  hrepClass : σ.arrs "repClass" = arrOf n repClass
  hrepsB : σ.arrs "repsB" = arrOf n repsB
  hnextB : σ.arrs "nextB" = arrOf n nextB
  hrepB : σ.arrs "repB" = arrOf n repB
  henum : PrefixEnumerates sampleCount ord Wnum
  hWrange : ∀ v ∈ Wnum, v < n
  hWfull : finsetOfNumeric Wnum = A
  hCactive : ∀ v : Fin n, v ∈ C ↔ activeB v.val = 1
  hCnonempty : C.Nonempty
  hsampleCountN : sampleCount ≤ n
  hnB : n < B
  htargetCapB : targetCap < B
  honeB : 1 < B
  hactiveBBound : ∀ v < n, activeB v < B

private lemma numericSet_eq_A {n : ℕ} {Wnum : Finset ℕ}
    {A : Finset (Fin n)} (h : finsetOfNumeric Wnum = A) :
    finSetAsSet Wnum = (A : Set (Fin n)) := by
  rw [← coe_finsetOfNumeric (n := n) Wnum, h]

private lemma finiteNeighborhood_coe_eq_trace {n : ℕ}
    (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n) :
    ((finiteNeighborhood G A v : Finset (Fin n)) : Set (Fin n)) =
      neighborhoodTrace G (A : Set (Fin n)) v := by
  ext u
  simp only [finiteNeighborhood, Finset.mem_coe, Finset.mem_filter,
    neighborhoodTrace, Set.mem_inter_iff, SimpleGraph.mem_neighborSet]
  exact and_comm

/-- The image map gives an equivalence of the corresponding finite subtypes. -/
noncomputable def imageSubtypeEquiv {α β : Type*} [DecidableEq α]
    [DecidableEq β] (X : Finset α) (f : α → β)
    (hinj : Set.InjOn f (X : Set α)) :
    {x // x ∈ X} ≃ {y // y ∈ X.image f} := by
  classical
  exact Equiv.ofBijective
      (fun x => (⟨f x.val, Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩⟩ :
        {y // y ∈ X.image f}))
      ⟨(by
        intro x y hxy
        apply Subtype.ext
        exact hinj x.property y.property (congrArg Subtype.val hxy)),
       (by
        intro y
        rcases Finset.mem_image.mp y.property with ⟨x, hx, hxy⟩
        exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩)⟩

/-- An injective image preserves the cardinality of its source. -/
lemma image_card_eq {α β : Type*} [DecidableEq α] [DecidableEq β]
    (X : Finset α) (f : α → β) (hinj : Set.InjOn f (X : Set α)) :
    X.card = (X.image f).card := by
  simpa using Fintype.card_congr (imageSubtypeEquiv X f hinj)

/-- Transport an enumeration through an injective image. -/
noncomputable def imageDomainEnumeration {α β : Type*} [DecidableEq α]
    [DecidableEq β] (X : Finset α) (f : α → β)
    (hinj : Set.InjOn f (X : Set α)) (enum : DomainEnumeration X) :
    DomainEnumeration (X.image f) :=
  (finEquivOfEq (image_card_eq X f hinj).symm).trans
    (enum.trans (imageSubtypeEquiv X f hinj))

/-- The image enumeration applies the map at the input index, with only a
cardinality cast between the two finite index types. -/
lemma imageDomainEnumeration_lookup {α β : Type*} [DecidableEq α]
    [DecidableEq β] (X : Finset α) (f : α → β)
    (hinj : Set.InjOn f (X : Set α)) (enum : DomainEnumeration X)
    (i : Fin (X.image f).card) :
    (imageDomainEnumeration X f hinj enum i).val =
      f (enum ((finEquivOfEq (image_card_eq X f hinj).symm) i)).val := by
  rfl

/-- Reinterpret the numeric representative set as its finite subset of `Fin n`. -/
noncomputable def numericRepresentativeSubtypeEquiv
    {n current : ℕ} {active label repClass reps outActive : ℕ → ℕ}
    {R : Finset ℕ} (hdata : RepData n current n active label repClass
      reps outActive R) : {r // r ∈ R} ≃
        {v // v ∈ finsetOfNumeric (n := n) R} := by
  classical
  exact Equiv.ofBijective
      (fun r => (⟨⟨r.val, (mem_activeVertices.mp
          (hdata.reps_processed r.property)).1⟩, by
        simp [finsetOfNumeric, r.property]⟩ :
          {v // v ∈ finsetOfNumeric (n := n) R}))
      ⟨(by
        intro r s hrs
        apply Subtype.ext
        exact congrArg (fun z : {v // v ∈ finsetOfNumeric (n := n) R} =>
          z.val.val) hrs),
       (by
        intro v
        refine ⟨⟨v.val.val, ?_⟩, ?_⟩
        · simpa [finsetOfNumeric] using v.property
        · apply Subtype.ext
          apply Fin.ext
          rfl)⟩

/-- The source and `Fin n` representative sets have the same cardinality. -/
lemma numericRepresentativeCard
    {n current : ℕ} {active label repClass reps outActive : ℕ → ℕ}
    {R : Finset ℕ} (hdata : RepData n current n active label repClass
      reps outActive R) :
    R.card = (finsetOfNumeric (n := n) R).card := by
  simpa using Fintype.card_congr (numericRepresentativeSubtypeEquiv hdata)

/-- Convert the source `RepData.enum` prefix to the corresponding `Fin n`
representatives without changing its order. -/
noncomputable def numericRepresentativeEnumeration
    {n current : ℕ} {active label repClass reps outActive : ℕ → ℕ}
    {R : Finset ℕ} (hdata : RepData n current n active label repClass
      reps outActive R) : DomainEnumeration (finsetOfNumeric (n := n) R) :=
  (finEquivOfEq (numericRepresentativeCard hdata).symm).trans
    ((prefixDomainEnumeration R.card reps R hdata.enum).trans
      (numericRepresentativeSubtypeEquiv hdata))

/-- The numeric representative enumeration follows the occupied source
`reps` prefix at every index. -/
lemma numericRepresentativeEnumeration_lookup
    {n current : ℕ} {active label repClass reps outActive : ℕ → ℕ}
    {R : Finset ℕ} (hdata : RepData n current n active label repClass
      reps outActive R) (i : Fin (finsetOfNumeric (n := n) R).card) :
    (numericRepresentativeEnumeration hdata i).val.val = reps i.val := by
  classical
  have hprefix := prefixDomainEnumeration_lookup R.card reps R hdata.enum
    ((finEquivOfEq (numericRepresentativeCard hdata).symm) i)
  change (prefixDomainEnumeration R.card reps R hdata.enum
      ((finEquivOfEq (numericRepresentativeCard hdata).symm) i)).val =
    reps i.val
  rw [hprefix]
  rfl

/-- Running `firstPartition` against every active vertex constructs the
actual source representative set and map, and makes its representatives
exactly the distinct full neighborhoods on `A`. -/
lemma runDistinctNeighborhoodSource
    {B n targetCap sampleCount : ℕ} {G : SimpleGraph (Fin n)}
    {x : List ℕ} {A C : Finset (Fin n)} {Wnum : Finset ℕ}
    (I : DistinctNeighborhoodInput B n targetCap sampleCount G x A C Wnum) :
    ∃ σ' current label repClass' repsB' nextB' repB' R,
      Run B (partition "activeB" "ord" "sampleCount" "classB"
        "repsB" "nextB" "repB" "nextBCount") I.σ σ'
        (partitionCost x I.ord n sampleCount) ∧
      σ'.vars "nextBCount" = R.card ∧
      σ'.arrs "activeB" = arrOf n I.activeB ∧
      σ'.arrs "classB" = arrOf n label ∧
      σ'.arrs "repClass" = arrOf n repClass' ∧
      σ'.arrs "repsB" = arrOf n repsB' ∧
      σ'.arrs "nextB" = arrOf n nextB' ∧
      σ'.arrs "repB" = arrOf n repB' ∧
      RepData n current n I.activeB label repClass' repsB' nextB' R ∧
      (∀ v < n, I.activeB v = 1 → repB' v = repClass' (label v)) ∧
      Nonempty (ConcreteTracePartition G I.activeB (A : Set (Fin n)) R repB') ∧
      (finsetOfNumeric (n := n) R : Set (Fin n)) ⊆ (C : Set (Fin n)) ∧
      Set.InjOn (finiteNeighborhood G A)
        (finsetOfNumeric (n := n) R : Set (Fin n)) ∧
      C.image (finiteNeighborhood G A) =
        (finsetOfNumeric (n := n) R).image (finiteNeighborhood G A) ∧
      (finsetOfNumeric (n := n) R).card =
        ((finsetOfNumeric (n := n) R).image (finiteNeighborhood G A)).card ∧
      partitionCost x I.ord n sampleCount ≤ 900 * (x.length + 1) := by
  classical
  have hactiveNonempty : (activeVertices n I.activeB).Nonempty := by
    obtain ⟨v, hv⟩ := I.hCnonempty
    exact ⟨v.val, mem_activeVertices.mpr ⟨v.isLt, (I.hCactive v).mp hv⟩⟩
  obtain ⟨σ', current, label, repClass', repsB', nextB', repB', R,
    hrun, hcount, hactive, hclass, hrepClass, hreps, hnextB, hrepB,
    hdata, hmap, htrace⟩ :=
      firstPartition_run I.hx I.htargetCap I.hn I.hsampleCount I.hoff
        I.htarget I.hactiveBArray I.hord I.hclassB I.hclassSize
        I.hmarkedCount I.hstamp I.hmarked I.htouched I.hsplit I.hrepClass
        I.hrepsB I.hnextB I.hrepB I.henum I.hWrange hactiveNonempty
        I.hsampleCountN I.hnB I.htargetCapB I.honeB I.hactiveBBound
  have htraceA : ConcreteTracePartition G I.activeB (A : Set (Fin n)) R repB' := by
    have hset := numericSet_eq_A I.hWfull
    rw [← hset]
    exact Classical.choice htrace
  let Rfin := finsetOfNumeric (n := n) R
  have hRset : (Rfin : Set (Fin n)) = finSetAsSet R :=
    coe_finsetOfNumeric (n := n) R
  have hRinC : (Rfin : Set (Fin n)) ⊆ (C : Set (Fin n)) := by
    intro r hr
    have hrR : r ∈ finSetAsSet R := by rw [← hRset]; exact hr
    have hractive := htraceA.partition.reps_mem hrR
    have hactive' : I.activeB r.val = 1 := by
      change r ∈ {v : Fin n | I.activeB v.val = 1} at hractive
      exact hractive
    exact (I.hCactive r).mpr hactive'
  have hinj : Set.InjOn (finiteNeighborhood G A) (Rfin : Set (Fin n)) := by
    intro u hu v hv huv
    have huR : u ∈ finSetAsSet R := by rw [← hRset]; exact hu
    have hvR : v ∈ finSetAsSet R := by rw [← hRset]; exact hv
    have htraceEq : neighborhoodTrace G (A : Set (Fin n)) u =
        neighborhoodTrace G (A : Set (Fin n)) v := by
      have hcoe := congrArg (fun X : Finset (Fin n) => (X : Set (Fin n))) huv
      simpa [finiteNeighborhood_coe_eq_trace] using hcoe
    exact htraceA.partition.reps_separated huR hvR htraceEq
  have himage : C.image (finiteNeighborhood G A) =
      Rfin.image (finiteNeighborhood G A) := by
    apply Finset.ext
    intro T
    constructor
    · intro hT
      rcases Finset.mem_image.mp hT with ⟨v, hv, rfl⟩
      let r := htraceA.partition.representative v
      have hrR : r ∈ finSetAsSet R :=
        htraceA.partition.representative_mem v ((I.hCactive v).mp hv)
      have hrV : r ∈ {u : Fin n | I.activeB u.val = 1} :=
        htraceA.partition.reps_mem hrR
      have hrC : r ∈ C := (I.hCactive r).mpr hrV
      have hrFin : r ∈ Rfin := by
        change r ∈ (Rfin : Set (Fin n))
        rw [hRset]
        exact hrR
      have hsame := htraceA.partition.same_trace v ((I.hCactive v).mp hv)
      have hneigh : finiteNeighborhood G A r = finiteNeighborhood G A v := by
        apply Finset.coe_injective
        simpa [finiteNeighborhood_coe_eq_trace] using hsame
      exact Finset.mem_image.mpr ⟨r, hrFin, hneigh⟩
    · intro hT
      rcases Finset.mem_image.mp hT with ⟨r, hr, hT⟩
      exact Finset.mem_image.mpr ⟨r, hRinC hr, hT⟩
  have hcard : Rfin.card = (Rfin.image (finiteNeighborhood G A)).card := by
    symm
    exact Finset.card_image_iff.mpr (by
      intro u hu v hv huv
      exact hinj hu hv huv)
  have hcost := partitionCost_le_input I.hx I.hsampleCountN
    (PrefixEnumerates.entry_lt I.henum I.hWrange)
    I.henum.injective_on_prefix
  refine ⟨σ', current, label, repClass', repsB', nextB', repB', R,
    hrun, hcount, hactive, hclass, hrepClass, hreps, hnextB, hrepB,
    hdata, hmap, ⟨htraceA⟩, hRinC, hinj, himage, hcard, hcost⟩

end

end Lax457868Proofs.DistinctNeighborhoodDomain
