import Lax457868Proofs.RepairDomainSource
import Lax457868Proofs.EnumeratedDraws
import Mathlib.Data.Finset.SymmDiff

/-! A degree-local append/filter over an already collected, duplicate-free
neighbor list. -/

namespace Lax457868Proofs.RepairFilterSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram
open Lax457868Proofs.EnumeratedDraws
open Lax457868Proofs.RepairDomainSource
open Lax457868Proofs.SourceRenaming
open Lax457868Proofs.ReusedOriginal.Construction.NearCollectSource
open Lax457868Proofs.ReusedOriginal.Construction.NeighborScan
open Lax11.GraphEncoding
open Lax11Proofs.CC
open Lax457868Proofs.SamplerPhases
open Lax457868Proofs.ExceptionRefinementStep
open Lax457868Proofs.ExceptionPhaseSource
open scoped symmDiff

noncomputable section

/-- The part of a collected list prefix whose opposite-side mark is zero. -/
def selectedPrefix (xs : List ℕ) (marks : ℕ → ℕ) (i : ℕ) : Finset ℕ :=
  (xs.take i).toFinset.filter fun v => marks v = 0

lemma selectedPrefix_succ (xs : List ℕ) (marks : ℕ → ℕ)
    {i : ℕ} (hi : i < xs.length) :
    selectedPrefix xs marks (i + 1) =
      if marks xs[i] = 0 then
        insert xs[i] (selectedPrefix xs marks i)
      else selectedPrefix xs marks i := by
  change ((xs.take (i + 1)).toFinset.filter fun v => marks v = 0) =
    if marks xs[i] = 0 then
      insert xs[i] ((xs.take i).toFinset.filter fun v => marks v = 0)
    else (xs.take i).toFinset.filter fun v => marks v = 0
  simp only [List.take_succ_eq_append_getElem hi, List.toFinset_append,
    Finset.filter_union]
  by_cases hm : marks xs[i] = 0 <;>
    simp [hm, Finset.filter_singleton, Finset.union_singleton]

lemma selectedPrefix_mono (xs : List ℕ) (marks : ℕ → ℕ)
    {i j : ℕ} (hij : i ≤ j) :
    selectedPrefix xs marks i ⊆ selectedPrefix xs marks j := by
  intro v hv
  simp only [selectedPrefix, Finset.mem_filter, List.mem_toFinset] at hv ⊢
  exact ⟨(List.take_sublist_take_left hij).mem hv.1, hv.2⟩

lemma selectedPrefix_full (xs : List ℕ) (marks : ℕ → ℕ) :
    selectedPrefix xs marks xs.length =
      xs.toFinset.filter fun v => marks v = 0 := by
  simp [selectedPrefix]

lemma getElem_not_mem_take_of_nodup {xs : List ℕ} (hxs : xs.Nodup)
    {i : ℕ} (hi : i < xs.length) : xs[i] ∉ xs.take i := by
  have htake : (xs.take (i + 1)).Nodup := hxs.take
  rw [List.take_succ_eq_append_getElem hi] at htake
  have hdisj := (List.nodup_append.mp htake).2.2
  intro hmem
  exact hdisj xs[i] hmem xs[i] (by simp) rfl

/-- Dynamic list filtering appends each value absent from the other
neighborhood to the occupied draw-domain prefix. -/
def appendFilteredTest (srcName marksName : String) : Cond :=
  .eq (.get marksName (.get srcName (.var "repairCursor"))) (.lit 0)

def appendFilteredBody (srcName marksName : String) : Com :=
  seqs [
    .ite (appendFilteredTest srcName marksName)
      (seqs [
        .store "drawDomain" (.var "drawModulus")
          (.get srcName (.var "repairCursor")),
        inc "drawModulus"])
      .skip,
    inc "repairCursor"]

def appendFilteredBodyCost (srcName marksName : String) : ℕ :=
  1 + (appendFilteredTest srcName marksName).size + 10 + 4

def appendFiltered (srcName marksName lenName : String) : Com :=
  seqs [
    .assign "repairCursor" (.lit 0),
    .while (.lt (.var "repairCursor") (.var lenName))
      (appendFilteredBody srcName marksName)]

def appendBOnly : Com :=
  appendFiltered "repairBList" "repairRMarks" "repairBLen"

def appendROnly : Com :=
  appendFiltered "repairRList" "repairBMarks" "repairRLen"

/-- The output prefix after scanning `repairCursor` source entries. -/
def FilterInv (n h : ℕ) (srcName marksName lenName : String)
    (src marks : ℕ → ℕ) (xs : List ℕ) (U : Finset ℕ)
    (τ : Env) : Prop :=
  τ.vars "n" = n ∧ τ.vars lenName = h ∧
  τ.arrs srcName = arrOf n src ∧
  τ.arrs marksName = arrOf n marks ∧
  τ.vars "repairCursor" ≤ h ∧
  ∃ out, τ.arrs "drawDomain" = arrOf n out ∧
    PrefixEnumerates (τ.vars "drawModulus") out
      (U ∪ selectedPrefix xs marks (τ.vars "repairCursor"))

private lemma appendFilteredBody_run
    {B n h : ℕ} {src marks : ℕ → ℕ} {xs : List ℕ}
    {S U : Finset ℕ} {σ : Env}
    {srcName marksName lenName : String}
    (hNames : srcName ≠ "drawDomain" ∧ marksName ≠ "drawDomain" ∧
      lenName ≠ "repairCursor" ∧ lenName ≠ "drawModulus" ∧
      lenName ≠ "n")
    (hI : FilterInv n h srcName marksName lenName src marks xs U σ)
    (hcursor : σ.vars "repairCursor" < h)
    (hxs : xs = Stack.toList h src) (hxsNodup : xs.Nodup)
    (hS : PrefixEnumerates h src S)
    (hSrange : S ⊆ Finset.range n)
    (hhn : h ≤ n)
    (hmarks01 : ∀ v < n, marks v ≤ 1)
    (hdisj : Disjoint U (selectedPrefix xs marks h))
    (hcap : (U ∪ selectedPrefix xs marks h).card ≤ n)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ', Run B (appendFilteredBody srcName marksName) σ σ'
        (appendFilteredBodyCost srcName marksName) ∧
      FilterInv n h srcName marksName lenName src marks xs U σ' ∧
      σ'.vars "repairCursor" = σ.vars "repairCursor" + 1 := by
  rcases hI with ⟨hn, hlen, hsrc, hmarks, hcursorLe, out, hout, hprefix⟩
  let i := σ.vars "repairCursor"
  let v := src i
  let k := σ.vars "drawModulus"
  let E := U ∪ selectedPrefix xs marks i
  have hi : i < h := hcursor
  have hiN : i < n := lt_of_lt_of_le hi hhn
  have hiB : i < B := hiN.trans hnB
  have hxsLen : xs.length = h := by simp [hxs, Stack.toList]
  have hlookup : xs[i] = v := by
    subst xs
    simp [Stack.toList, arrOf, v]
  have hvN : v < n := by
    have hiXs : i < xs.length := by rw [hxsLen]; exact hi
    have hvXs : v ∈ xs := by
      rw [← hlookup]
      exact List.getElem_mem hiXs
    have hvS : v ∈ S := (hS.2 v).mp (by simpa [hxs] using hvXs)
    exact Finset.mem_range.mp (hSrange hvS)
  have hvB : v < B := hvN.trans hnB
  have hmB : marks v < B := by have := hmarks01 v hvN; omega
  have hsrcEval : (Expr.get srcName (.var "repairCursor")).evalB B σ =
      some v := by
    apply evalB_get
    · exact evalB_var (by simpa [i] using hiB)
    · rw [hsrc, getElem?_arrOf src hiN]
    · exact hvB
  have hmarksEval : (Expr.get marksName
      (.get srcName (.var "repairCursor"))).evalB B σ =
      some (marks v) := by
    apply evalB_get hsrcEval
    · rw [hmarks, getElem?_arrOf marks hvN]
    · exact hmB
  have htest : (appendFilteredTest srcName marksName).evalB B σ =
      some (marks v == 0) := by
    simpa [appendFilteredTest] using
      evalB_condEq hmarksEval (evalB_lit (by omega : 0 < B))
  by_cases hm0 : marks v = 0
  · have htestTrue : (appendFilteredTest srcName marksName).evalB B σ =
        some true := by simpa [hm0] using htest
    have hvNotTake : v ∉ xs.take i := by
      rw [← hlookup]
      exact getElem_not_mem_take_of_nodup hxsNodup (by rw [hxsLen]; exact hi)
    have hvNotF : v ∉ selectedPrefix xs marks i := by
      simp only [selectedPrefix, Finset.mem_filter, List.mem_toFinset]
      intro hv
      exact hvNotTake hv.1
    have hvFull : v ∈ selectedPrefix xs marks h := by
      have hnext := selectedPrefix_succ xs marks
        (i := i) (by rw [hxsLen]; exact hi)
      rw [hlookup, hm0] at hnext
      have hmemNext : v ∈ selectedPrefix xs marks (i + 1) := by
        rw [hnext]; simp
      exact selectedPrefix_mono xs marks (by omega : i + 1 ≤ h) hmemNext
    have hvNotU : v ∉ U := by
      intro hu
      exact (Finset.disjoint_left.mp hdisj) hu hvFull
    have hvNotE : v ∉ E := by
      simp [E, hvNotU, hvNotF]
    have hnextSet : U ∪ selectedPrefix xs marks (i + 1) = insert v E := by
      rw [selectedPrefix_succ xs marks (by rw [hxsLen]; exact hi),
        hlookup, hm0]
      simp [E, Finset.union_insert]
    have hECard : k = E.card := prefixEnumerates_card k out E hprefix
    have hkN : k < n := by
      have hsub : insert v E ⊆ U ∪ selectedPrefix xs marks h := by
        rw [← hnextSet]
        intro w hw
        rcases Finset.mem_union.mp hw with hU | hF
        · exact Finset.mem_union_left _ hU
        · exact Finset.mem_union_right _
            (selectedPrefix_mono xs marks (by omega : i + 1 ≤ h) hF)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hvNotE, ← hECard] at hc
      omega
    have hkB : k < B := hkN.trans hnB
    let σ₁ := σ.setArr "drawDomain" k v
    have rstore : Run B
        (.store "drawDomain" (.var "drawModulus")
          (.get srcName (.var "repairCursor"))) σ σ₁ 5 := by
      have hidx : (Expr.var "drawModulus").evalB B σ = some k :=
        evalB_var (by simpa [k] using hkB)
      have hraw := Run.store hidx hsrcEval
        (by rw [hout, length_arrOf]; exact hkN)
      exact hraw.mono (by norm_num [Expr.size])
    let σ₂ := σ₁.setVar "drawModulus" (k + 1)
    have rmod : Run B (inc "drawModulus") σ₁ σ₂ 4 := by
      have hvar : (Expr.var "drawModulus").evalB B σ₁ = some k := by
        apply evalB_var
        simpa [σ₁, k] using hkB
      have hadd : (Expr.add (.var "drawModulus") (.lit 1)).evalB B σ₁ =
          some (k + 1) := by
        apply evalB_bin hvar (evalB_lit honeB)
        change k + 1 < B
        omega
      simpa [inc, σ₂] using Run.assign hadd
    have hbranch : Run B
        (seqs [.store "drawDomain" (.var "drawModulus")
            (.get srcName (.var "repairCursor")), inc "drawModulus"])
        σ σ₂ 9 := by simpa [seqs] using rstore.seq rmod
    have hite : Run B
        (.ite (appendFilteredTest srcName marksName)
          (seqs [.store "drawDomain" (.var "drawModulus")
              (.get srcName (.var "repairCursor")), inc "drawModulus"])
          .skip) σ σ₂
        (1 + (appendFilteredTest srcName marksName).size + 9) :=
      Run.ite_true htestTrue hbranch
    let σ₃ := σ₂.setVar "repairCursor" (i + 1)
    have rcursor : Run B (inc "repairCursor") σ₂ σ₃ 4 := by
      have hcur₂ : σ₂.vars "repairCursor" = i := by simp [σ₂, σ₁, i]
      have hcurEval : (Expr.add (.var "repairCursor") (.lit 1)).evalB B
          σ₂ = some (i + 1) := by
        apply evalB_bin
        · exact evalB_var (by rw [hcur₂]; exact hiB)
        · exact evalB_lit honeB
        · change i + 1 < B
          omega
      simpa [inc, σ₃] using Run.assign hcurEval
    have hrun : Run B (appendFilteredBody srcName marksName) σ σ₃
        (appendFilteredBodyCost srcName marksName) := by
      have hseq := hite.seq rcursor
      exact (show Run B (appendFilteredBody srcName marksName) σ σ₃
          (1 + (appendFilteredTest srcName marksName).size + 9 + 4) by
            simpa [appendFilteredBody, seqs] using hseq).mono
        (by unfold appendFilteredBodyCost; omega)
    let out' := upd out k v
    have hout₃ : σ₃.arrs "drawDomain" = arrOf n out' := by
      simp [σ₃, σ₂, σ₁, hout, out', set_arrOf_eq_upd]
    have hprefix₃ : PrefixEnumerates (σ₃.vars "drawModulus") out'
        (U ∪ selectedPrefix xs marks (σ₃.vars "repairCursor")) := by
      have hp := hprefix.push hvNotE
      simpa [σ₃, σ₂, σ₁, hnextSet, out', i, k] using hp
    refine ⟨σ₃, hrun, ?_, by simp [σ₃, σ₂, σ₁, i]⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, out', hout₃, hprefix₃⟩
    · exact (hrun.frame_var "n" (by
        simp [appendFilteredBody, seqs, inc, Com.wvars])).trans hn
    · exact (hrun.frame_var lenName (by
        simp [appendFilteredBody, seqs, inc, Com.wvars,
          hNames.2.2.1, hNames.2.2.2.1])).trans hlen
    · exact (hrun.frame_arr srcName (by
        simp [appendFilteredBody, seqs, inc, Com.warrs,
          hNames.1])).trans hsrc
    · exact (hrun.frame_arr marksName (by
        simp [appendFilteredBody, seqs, inc, Com.warrs,
          hNames.2.1])).trans hmarks
    · simp [σ₃, i]
      omega
  · have htestFalse : (appendFilteredTest srcName marksName).evalB B σ =
        some false := by
      have hfalse : (marks v == 0) = false := by
        cases hbool : (marks v == 0) with
        | false => rfl
        | true =>
            have heq : marks v = 0 := by simpa using hbool
            exact False.elim (hm0 heq)
      rw [hfalse] at htest
      exact htest
    let σ₁ := σ.setVar "repairCursor" (i + 1)
    have rcursor : Run B (inc "repairCursor") σ σ₁ 4 := by
      have hcurEval : (Expr.add (.var "repairCursor") (.lit 1)).evalB B
          σ = some (i + 1) := by
        apply evalB_bin
        · exact evalB_var (by simpa [i] using hiB)
        · exact evalB_lit honeB
        · change i + 1 < B
          omega
      simpa [inc, σ₁] using Run.assign hcurEval
    have hite : Run B
        (.ite (appendFilteredTest srcName marksName)
          (seqs [.store "drawDomain" (.var "drawModulus")
              (.get srcName (.var "repairCursor")), inc "drawModulus"])
          .skip) σ σ (1 + (appendFilteredTest srcName marksName).size + 1) :=
      Run.ite_false htestFalse Run.skip
    have hrun : Run B (appendFilteredBody srcName marksName) σ σ₁
        (appendFilteredBodyCost srcName marksName) := by
      have hseq := hite.seq rcursor
      exact (show Run B (appendFilteredBody srcName marksName) σ σ₁
          (1 + (appendFilteredTest srcName marksName).size + 1 + 4) by
            simpa [appendFilteredBody, seqs] using hseq).mono
        (by unfold appendFilteredBodyCost; omega)
    have hnextSet : selectedPrefix xs marks (i + 1) =
        selectedPrefix xs marks i := by
      rw [selectedPrefix_succ xs marks (by rw [hxsLen]; exact hi),
        hlookup, if_neg hm0]
    refine ⟨σ₁, hrun, ?_, by simp [σ₁, i]⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, out, ?_, ?_⟩
    · simp [σ₁, hn]
    · simp [σ₁, hlen, hNames.2.2.1]
    · simp [σ₁, hsrc]
    · simp [σ₁, hmarks]
    · simp [σ₁, i]
      omega
    · simpa [σ₁] using hout
    · simpa [σ₁, hnextSet, i] using hprefix

/-- One whole filtered append pass charges only the length of its collected
neighbor list. It keeps every array except `drawDomain` intact. -/
lemma appendFiltered_run
    {B n h : ℕ} {src marks domain : ℕ → ℕ}
    {S U : Finset ℕ} {σ : Env}
    {srcName marksName lenName : String}
    (hNames : srcName ≠ "drawDomain" ∧ marksName ≠ "drawDomain" ∧
      lenName ≠ "repairCursor" ∧ lenName ≠ "drawModulus" ∧
      lenName ≠ "n")
    (hn : σ.vars "n" = n) (hlen : σ.vars lenName = h)
    (hsrc : σ.arrs srcName = arrOf n src)
    (hmarks : σ.arrs marksName = arrOf n marks)
    (hdomain : σ.arrs "drawDomain" = arrOf n domain)
    (hprefix : PrefixEnumerates (σ.vars "drawModulus") domain U)
    (hS : PrefixEnumerates h src S) (hSrange : S ⊆ Finset.range n)
    (hhn : h ≤ n) (hmarks01 : ∀ v < n, marks v ≤ 1)
    (hdisj : Disjoint U (selectedPrefix (Stack.toList h src) marks h))
    (hcap : (U ∪ selectedPrefix (Stack.toList h src) marks h).card ≤ n)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ' out',
      Run B (appendFiltered srcName marksName lenName) σ σ'
        ((appendFilteredBodyCost srcName marksName + 4) * h + 6) ∧
      σ'.arrs "drawDomain" = arrOf n out' ∧
      PrefixEnumerates (σ'.vars "drawModulus") out'
        (U ∪ selectedPrefix (Stack.toList h src) marks h) ∧
      σ'.vars "drawModulus" =
        (U ∪ selectedPrefix (Stack.toList h src) marks h).card ∧
      σ'.vars "repairCursor" = h ∧
      σ'.arrs srcName = arrOf n src ∧
      σ'.arrs marksName = arrOf n marks ∧
      σ'.vars lenName = h ∧ σ'.vars "n" = n ∧
      (∀ a, a ≠ "drawDomain" → σ'.arrs a = σ.arrs a) ∧
      (∀ v, v ≠ "repairCursor" → v ≠ "drawModulus" →
        σ'.vars v = σ.vars v) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let xs := Stack.toList h src
  let I := FilterInv n h srcName marksName lenName src marks xs U
  have hbody : Spec B
      (fun τ => I τ ∧ τ.vars "repairCursor" < h)
      (appendFilteredBody srcName marksName)
      (fun τ τ' => I τ' ∧
        τ'.vars "repairCursor" = τ.vars "repairCursor" + 1)
      (appendFilteredBodyCost srcName marksName) := by
    intro τ ⟨hI, hcur⟩
    exact appendFilteredBody_run hNames hI hcur rfl hS.1
      hS hSrange hhn hmarks01 hdisj hcap hnB honeB
  have hloop := Spec.forRangeZero "repairCursor" lenName I h
      (appendFilteredBodyCost srcName marksName)
      (lt_of_le_of_lt hhn hnB)
      (by intro τ hI; exact hI.2.2.2.2.1)
      (by intro τ hI; exact hI.2.1)
      hbody
  have hstart : I (σ.setVar "repairCursor" 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, domain, ?_, ?_⟩
    · simpa [I, FilterInv] using hn
    · simpa [I, FilterInv, hNames.2.2.1] using hlen
    · simpa [I, FilterInv] using hsrc
    · simpa [I, FilterInv] using hmarks
    · simp
    · simpa using hdomain
    · simpa [selectedPrefix, I] using hprefix
  obtain ⟨σ', rloop, hfinal, hcursor⟩ := hloop.run hstart
  have hrun : Run B (appendFiltered srcName marksName lenName) σ σ'
      ((appendFilteredBodyCost srcName marksName + 4) * h + 6) := by
    simpa [appendFiltered, seqs] using rloop
  rcases hfinal with ⟨hn', hlen', hsrc', hmarks', _hcurLe,
    out', hdomain', hprefix'⟩
  have hcount := prefixEnumerates_card (σ'.vars "drawModulus") out'
    (U ∪ selectedPrefix xs marks h) (by simpa [hcursor] using hprefix')
  refine ⟨σ', out', hrun, hdomain', ?_, ?_, hcursor,
    hsrc', hmarks', hlen', hn', ?_, ?_, ?_, ?_⟩
  · simpa [xs, hcursor] using hprefix'
  · simpa [xs] using hcount
  · intro a ha
    exact hrun.frame_arr a (by
      simp [appendFiltered, appendFilteredBody, seqs, inc, Com.warrs, ha])
  · intro v hvc hvm
    exact hrun.frame_var v (by
      simp [appendFiltered, appendFilteredBody, seqs, inc,
        Com.wvars, hvc, hvm])
  · exact hrun.frame_inp (by
      simp [appendFiltered, appendFilteredBody, seqs, inc, Com.reads])
  · exact hrun.out_eq (by
      simp [appendFiltered, appendFilteredBody, seqs, inc, Com.NoWrite])

/-- A zero-one mark array converts the filter's zero test to set
difference. -/
lemma selectedPrefix_eq_sdiff
    {n h : ℕ} {src marks : ℕ → ℕ} {S T : Finset ℕ}
    (hS : PrefixEnumerates h src S)
    (hSrange : S ⊆ Finset.range n)
    (hmarks01 : ∀ v < n, marks v ≤ 1)
    (hmarksMem : ∀ v < n, marks v = 1 ↔ v ∈ T) :
    selectedPrefix (Stack.toList h src) marks h = S \ T := by
  ext v
  have hfull : selectedPrefix (Stack.toList h src) marks h =
      (Stack.toList h src).toFinset.filter fun w => marks w = 0 := by
    simpa using selectedPrefix_full (Stack.toList h src) marks
  rw [hfull]
  simp only [Finset.mem_filter, Finset.mem_sdiff, List.mem_toFinset]
  have hvS : v ∈ Stack.toList h src ↔ v ∈ S := hS.2 v
  constructor
  · rintro ⟨hv, hm0⟩
    refine ⟨hvS.mp hv, ?_⟩
    have hvN : v < n := Finset.mem_range.mp (hSrange (hvS.mp hv))
    intro hvT
    have hm1 := (hmarksMem v hvN).mpr hvT
    omega
  · rintro ⟨hv, hvNotT⟩
    have hvN : v < n := Finset.mem_range.mp (hSrange hv)
    have hmNe : marks v ≠ 1 := by
      intro hm1
      exact hvNotT ((hmarksMem v hvN).mp hm1)
    have hm0 : marks v = 0 := by have := hmarks01 v hvN; omega
    exact ⟨hvS.mpr hv, hm0⟩

/-- The two stable filters append precisely the symmetric difference of
the already collected neighborhood sets. The output buffer has capacity
`n` because both neighborhoods lie in the vertex range. -/
def appendSymmetricDifference : Com :=
  seqs [.assign "drawModulus" (.lit 0), appendBOnly, appendROnly]

lemma appendSymmetricDifference_run
    {B n hb hr : ℕ} {σ : Env}
    {blist rlist bmarks rmarks domain : ℕ → ℕ}
    {BS RS : Finset ℕ}
    (hn : σ.vars "n" = n)
    (hblen : σ.vars "repairBLen" = hb)
    (hrlen : σ.vars "repairRLen" = hr)
    (hblist : σ.arrs "repairBList" = arrOf n blist)
    (hrlist : σ.arrs "repairRList" = arrOf n rlist)
    (hbmarks : σ.arrs "repairBMarks" = arrOf n bmarks)
    (hrmarks : σ.arrs "repairRMarks" = arrOf n rmarks)
    (hdomain : σ.arrs "drawDomain" = arrOf n domain)
    (hB : PrefixEnumerates hb blist BS)
    (hR : PrefixEnumerates hr rlist RS)
    (hBrange : BS ⊆ Finset.range n)
    (hRrange : RS ⊆ Finset.range n)
    (hb01 : ∀ v < n, bmarks v ≤ 1)
    (hr01 : ∀ v < n, rmarks v ≤ 1)
    (hbmem : ∀ v < n, bmarks v = 1 ↔ v ∈ BS)
    (hrmem : ∀ v < n, rmarks v = 1 ↔ v ∈ RS)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ' domain',
      Run B appendSymmetricDifference σ σ' (24 * (hb + hr) + 14) ∧
      σ'.arrs "drawDomain" = arrOf n domain' ∧
      PrefixEnumerates (σ'.vars "drawModulus") domain' (BS ∆ RS) ∧
      σ'.vars "drawModulus" = (BS ∆ RS).card ∧
      (BS ∆ RS) ⊆ Finset.range n ∧
      σ'.arrs "repairBList" = arrOf n blist ∧
      σ'.arrs "repairRList" = arrOf n rlist ∧
      σ'.arrs "repairBMarks" = arrOf n bmarks ∧
      σ'.arrs "repairRMarks" = arrOf n rmarks ∧
      σ'.vars "repairBLen" = hb ∧ σ'.vars "repairRLen" = hr ∧
      σ'.vars "n" = n ∧
      (∀ a, a ≠ "drawDomain" → σ'.arrs a = σ.arrs a) ∧
      (∀ v, v ≠ "drawModulus" → v ≠ "repairCursor" →
        σ'.vars v = σ.vars v) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  have hBonly := selectedPrefix_eq_sdiff hB hBrange hr01 hrmem
  have hRonly := selectedPrefix_eq_sdiff hR hRrange hb01 hbmem
  have hXrange : BS ∆ RS ⊆ Finset.range n := by
    rw [Finset.symmDiff_def]
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hBrange (Finset.mem_sdiff.mp hv).1
    · exact hRrange (Finset.mem_sdiff.mp hv).1
  have hcapX : (BS ∆ RS).card ≤ n := by
    simpa using Finset.card_le_card hXrange
  have hcapB : (BS \ RS).card ≤ n := by
    have hsub : BS \ RS ⊆ Finset.range n :=
      (Finset.sdiff_subset).trans hBrange
    simpa using Finset.card_le_card hsub
  have hdisj : Disjoint (BS \ RS) (RS \ BS) := by
    apply Finset.disjoint_left.mpr
    intro v hvB hvR
    exact (Finset.mem_sdiff.mp hvB).2 (Finset.mem_sdiff.mp hvR).1
  let σ₀ := σ.setVar "drawModulus" 0
  have rzero : Run B (.assign "drawModulus" (.lit 0)) σ σ₀ 2 := by
    simpa [σ₀] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have hprefix0 : PrefixEnumerates (σ₀.vars "drawModulus") domain ∅ := by
    simp [σ₀, prefixEnumerates_zero]
  obtain ⟨σ₁, domain₁, rB, hdomain₁, hprefix₁,
    hcount₁, _hcursorB, _hblist₁, _hrmarks₁,
    _hblen₁, hn₁, hframeB, hvarsB, _hinpB, _houtB⟩ :=
    appendFiltered_run
      (srcName := "repairBList") (marksName := "repairRMarks")
      (lenName := "repairBLen") (S := BS) (U := ∅)
      (by decide) (by simpa [σ₀] using hn)
      (by simpa [σ₀] using hblen)
      (by simpa [σ₀] using hblist)
      (by simpa [σ₀] using hrmarks)
      (by simpa [σ₀] using hdomain)
      hprefix0 hB hBrange
      (by rw [prefixEnumerates_card hb blist BS hB];
          simpa using Finset.card_le_card hBrange)
      hr01
      (by simp [hBonly])
      (by simpa [hBonly] using hcapB)
      hnB honeB
  have hprefixB : PrefixEnumerates (σ₁.vars "drawModulus") domain₁
      (BS \ RS) := by simpa [hBonly] using hprefix₁
  have hrlen₁ : σ₁.vars "repairRLen" = hr := by
    rw [hvarsB "repairRLen" (by decide) (by decide)]
    simpa [σ₀] using hrlen
  have hrlist₁ : σ₁.arrs "repairRList" = arrOf n rlist := by
    rw [hframeB "repairRList" (by decide)]
    simpa [σ₀] using hrlist
  have hbmarks₁ : σ₁.arrs "repairBMarks" = arrOf n bmarks := by
    rw [hframeB "repairBMarks" (by decide)]
    simpa [σ₀] using hbmarks
  obtain ⟨σ₂, domain₂, rR, hdomain₂, hprefix₂,
    hcount₂, _hcursorR, _hrlist₂, _hbmarks₂,
    _hrlen₂, hn₂, hframeR, hvarsR, _hinpR, _houtR⟩ :=
    appendFiltered_run
      (srcName := "repairRList") (marksName := "repairBMarks")
      (lenName := "repairRLen") (S := RS) (U := BS \ RS)
      (by decide) hn₁ hrlen₁ hrlist₁ hbmarks₁ hdomain₁
      hprefixB hR hRrange
      (by rw [prefixEnumerates_card hr rlist RS hR];
          simpa using Finset.card_le_card hRrange)
      hb01 (by simpa [hRonly] using hdisj)
      (by simpa [hRonly, Finset.symmDiff_def] using hcapX)
      hnB honeB
  have hrun : Run B appendSymmetricDifference σ σ₂
      (24 * (hb + hr) + 14) := by
    have hseq := rzero.seq (rB.seq rR)
    have hbound : 2 +
        (((appendFilteredBodyCost "repairBList" "repairRMarks" + 4) * hb + 6) +
          ((appendFilteredBodyCost "repairRList" "repairBMarks" + 4) * hr + 6)) ≤
        24 * (hb + hr) + 14 := by
      norm_num [appendFilteredBodyCost, appendFilteredTest,
        Cond.size, Expr.size]
      omega
    simpa [appendSymmetricDifference, appendBOnly, appendROnly,
      seqs] using hseq.mono hbound
  have hprefixX : PrefixEnumerates (σ₂.vars "drawModulus") domain₂
      (BS ∆ RS) := by
    simpa [hRonly, Finset.symmDiff_def] using hprefix₂
  have hcountX : σ₂.vars "drawModulus" = (BS ∆ RS).card := by
    simpa [hRonly, Finset.symmDiff_def] using hcount₂
  refine ⟨σ₂, domain₂, hrun, hdomain₂, hprefixX, hcountX,
    hXrange, ?_, ?_, ?_, ?_, ?_, ?_, hn₂, ?_, ?_, ?_, ?_⟩
  · rw [hframeR "repairBList" (by decide),
      hframeB "repairBList" (by decide)]
    simpa [σ₀] using hblist
  · rw [hframeR "repairRList" (by decide),
      hframeB "repairRList" (by decide)]
    simpa [σ₀] using hrlist
  · rw [hframeR "repairBMarks" (by decide),
      hframeB "repairBMarks" (by decide)]
    simpa [σ₀] using hbmarks
  · rw [hframeR "repairRMarks" (by decide),
      hframeB "repairRMarks" (by decide)]
    simpa [σ₀] using hrmarks
  · rw [hvarsR "repairBLen" (by decide) (by decide),
      hvarsB "repairBLen" (by decide) (by decide)]
    simpa [σ₀] using hblen
  · rw [hvarsR "repairRLen" (by decide) (by decide),
      hvarsB "repairRLen" (by decide) (by decide)]
    simpa [σ₀] using hrlen
  · intro a ha
    exact hrun.frame_arr a (by
      simp [appendSymmetricDifference, appendBOnly, appendROnly,
        appendFiltered, appendFilteredBody, seqs, inc, Com.warrs, ha])
  · intro v hmod hcursor
    exact hrun.frame_var v (by
      simp [appendSymmetricDifference, appendBOnly, appendROnly,
        appendFiltered, appendFilteredBody, seqs, inc,
        Com.wvars, hmod, hcursor])
  · exact hrun.frame_inp (by
      simp [appendSymmetricDifference, appendBOnly, appendROnly,
        appendFiltered, appendFilteredBody, seqs, inc, Com.reads])
  · exact hrun.out_eq (by
      simp [appendSymmetricDifference, appendBOnly, appendROnly,
        appendFiltered, appendFilteredBody, seqs, inc, Com.NoWrite])

/-! The runtime repair builder reads its representative from the preserved
`repB` array and derives both active neighborhoods from CSR. -/

def repairDomainCore : Com :=
  seqs [
    .assign "repairRep" (.get "repB" (.var "repairB")),
    collectRepairBAt,
    collectRepairRAt,
    appendSymmetricDifference]

lemma repairDomainCore_run
    {B n targetCap b : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A : Finset ℕ} {rep blist rlist domain : ℕ → ℕ} {σ : Env}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (hA : A ⊆ Finset.range n)
    (hn : σ.vars "n" = n)
    (hbvar : σ.vars "repairB" = b)
    (hrep : σ.arrs "repB" = arrOf n rep)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactive : σ.arrs "activeA" = arrOf n (setFlag A))
    (hbmarks : σ.arrs "repairBMarks" = arrOf n (fun _ => 0))
    (hrmarks : σ.arrs "repairRMarks" = arrOf n (fun _ => 0))
    (hblist : σ.arrs "repairBList" = arrOf n blist)
    (hrlist : σ.arrs "repairRList" = arrOf n rlist)
    (hdomain : σ.arrs "drawDomain" = arrOf n domain)
    (hb : b < n) (hr : rep b < n)
    (hn1B : n + 1 < B) (htargetCapB : targetCap < B) :
    ∃ σ' domain' bmarks' rmarks' blist' rlist',
      Run B repairDomainCore σ σ'
        (54 * ((offset x (b + 1) - offset x b) +
            (offset x (rep b + 1) - offset x (rep b))) +
          24 * (((numericNeighborhood G b ∩ A).card) +
            ((numericNeighborhood G (rep b) ∩ A).card)) + 61) ∧
      σ'.arrs "drawDomain" = arrOf n domain' ∧
      σ'.vars "drawModulus" =
        ((numericNeighborhood G b ∩ A) ∆
          (numericNeighborhood G (rep b) ∩ A)).card ∧
      PrefixEnumerates (σ'.vars "drawModulus") domain'
        ((numericNeighborhood G b ∩ A) ∆
          (numericNeighborhood G (rep b) ∩ A)) ∧
      σ'.arrs "repairBMarks" = arrOf n bmarks' ∧
      σ'.arrs "repairRMarks" = arrOf n rmarks' ∧
      σ'.arrs "repairBList" = arrOf n blist' ∧
      σ'.arrs "repairRList" = arrOf n rlist' ∧
      σ'.vars "repairBLen" = (numericNeighborhood G b ∩ A).card ∧
      σ'.vars "repairRLen" = (numericNeighborhood G (rep b) ∩ A).card ∧
      (∀ v < n, bmarks' v = 1 ↔ v ∈ numericNeighborhood G b ∩ A) ∧
      (∀ v < n, rmarks' v = 1 ↔ v ∈ numericNeighborhood G (rep b) ∩ A) ∧
      (∀ v < n, bmarks' v ≤ 1) ∧
      (∀ v < n, rmarks' v ≤ 1) ∧
      PrefixEnumerates (numericNeighborhood G b ∩ A).card blist'
        (numericNeighborhood G b ∩ A) ∧
      PrefixEnumerates (numericNeighborhood G (rep b) ∩ A).card rlist'
        (numericNeighborhood G (rep b) ∩ A) ∧
      σ'.arrs "repB" = arrOf n rep ∧
      σ'.arrs "activeA" = arrOf n (setFlag A) ∧
      σ'.vars "n" = n ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let BS := numericNeighborhood G b ∩ A
  let RS := numericNeighborhood G (rep b) ∩ A
  have hAB : ∀ v < n, setFlag A v < B := by
    intro v hv
    by_cases hvA : v ∈ A <;> simp [setFlag, hvA] <;> omega
  have honeB : 1 < B := by omega
  let σ₀ := σ.setVar "repairRep" (rep b)
  have hevalRep : (Expr.get "repB" (.var "repairB")).evalB B σ =
      some (rep b) := by
    apply evalB_get
    · exact evalB_var (by rw [hbvar]; omega)
    · rw [hrep, hbvar]
      exact getElem?_arrOf rep hb
    · omega
  have rrep : Run B (.assign "repairRep" (.get "repB" (.var "repairB")))
      σ σ₀ 3 := by
    simpa [σ₀] using (Run.assign hevalRep)
  have hσ₀var : σ₀.vars "repairRep" = rep b := by simp [σ₀]
  have hσ₀arr : ∀ a, σ₀.arrs a = σ.arrs a := by
    intro a; rfl
  have hσ₀n : σ₀.vars "n" = n := by simpa [σ₀] using hn
  have hσ₀b : σ₀.vars "repairB" = b := by simpa [σ₀] using hbvar
  let ρB := repairCollectNames "repairBMarks" "repairBList" "repairBLen"
  let ρR := repairCollectNames "repairRMarks" "repairRList" "repairRLen"
  obtain ⟨σ₁, bm, bl, rB, hbm₁, hbl₁, hblen₁, henumB,
    hmemB, hboundB, _hactiveB, _htargetB, _hjB, _htokenB, _hinpB, _houtB⟩ :=
    collectNeighborhoodAt_run ρB "repairB" "activeA"
      "repairBMarks" "repairBList" "repairBLen"
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      hx htargetCap hσ₀b hσ₀n
      (by rw [hσ₀arr]; exact hoff)
      (by rw [hσ₀arr]; exact htarget)
      (by rw [hσ₀arr]; exact hactive)
      (by rw [hσ₀arr]; exact hbmarks)
      (by rw [hσ₀arr]; exact hblist)
      hb hAB hn1B htargetCapB
  have hkeepB (a : String) (ha : a ≠ "repairBMarks")
      (hal : a ≠ "repairBList") : σ₁.arrs a = σ₀.arrs a :=
    rB.frame_arr a (by
      simp [collectNeighborhoodAt, prepareNeighborAt, ρB,
        repairCollectNames, neighborhoodNames, renameCom,
        collectNeighborBody, seqs, inc, Com.warrs]
      change a ≠ "repairBMarks" ∧ a ≠ "repairBList"
      exact ⟨ha, hal⟩)
  have hkeepBVar (v : String) (hbtmp : v ≠ "b") (hj : v ≠ "j") (hjend : v ≠ "jend")
      (htok : v ≠ "token") (hlen : v ≠ "repairBLen") :
      σ₁.vars v = σ₀.vars v :=
    rB.frame_var v (by
      simp [collectNeighborhoodAt, prepareNeighborAt, ρB,
        repairCollectNames, neighborhoodNames, renameCom,
        collectNeighborBody, seqs, inc, Com.wvars, hj, hjend, htok, hlen]
      change v ≠ "b" ∧ v ≠ "j"
      exact ⟨hbtmp, hj⟩)
  have hσ₁rep : σ₁.vars "repairRep" = rep b := by
    rw [hkeepBVar "repairRep" (by decide) (by decide) (by decide)
      (by decide) (by decide)]
    exact hσ₀var
  have hσ₁n : σ₁.vars "n" = n := by
    rw [hkeepBVar "n" (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hσ₀n
  obtain ⟨σ₂, rm, rl, rR, hrm₂, hrl₂, hrlen₂, henumR,
    hmemR, hboundR, _hactiveR, _htargetR, _hjR, _htokenR, _hinpR, _houtR⟩ :=
    collectNeighborhoodAt_run ρR "repairRep" "activeA"
      "repairRMarks" "repairRList" "repairRLen"
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      hx htargetCap hσ₁rep hσ₁n
      (by rw [hkeepB "off" (by decide) (by decide), hσ₀arr]; exact hoff)
      (by rw [hkeepB "tgt" (by decide) (by decide), hσ₀arr]; exact htarget)
      (by rw [hkeepB "activeA" (by decide) (by decide), hσ₀arr]; exact hactive)
      (by rw [hkeepB "repairRMarks" (by decide) (by decide), hσ₀arr]; exact hrmarks)
      (by rw [hkeepB "repairRList" (by decide) (by decide), hσ₀arr]; exact hrlist)
      hr hAB hn1B htargetCapB
  have hkeepR (a : String) (ha : a ≠ "repairRMarks")
      (hal : a ≠ "repairRList") : σ₂.arrs a = σ₁.arrs a :=
    rR.frame_arr a (by
      simp [collectNeighborhoodAt, prepareNeighborAt, ρR,
        repairCollectNames, neighborhoodNames, renameCom,
        collectNeighborBody, seqs, inc, Com.warrs]
      change a ≠ "repairRMarks" ∧ a ≠ "repairRList"
      exact ⟨ha, hal⟩)
  have hkeepRVar (v : String) (hbtmp : v ≠ "b") (hj : v ≠ "j") (hjend : v ≠ "jend")
      (htok : v ≠ "token") (hlen : v ≠ "repairRLen") :
      σ₂.vars v = σ₁.vars v :=
    rR.frame_var v (by
      simp [collectNeighborhoodAt, prepareNeighborAt, ρR,
        repairCollectNames, neighborhoodNames, renameCom,
        collectNeighborBody, seqs, inc, Com.wvars, hj, hjend, htok, hlen]
      change v ≠ "b" ∧ v ≠ "j"
      exact ⟨hbtmp, hj⟩)
  have hBset :
      ReusedOriginal.Construction.NeighborScan.activeTargets
        (target x) (setFlag A) (offset x b) (offset x (b + 1)) = BS := by
    exact activeTargets_eq_numericNeighborhood_inter hx A b hb
  have hRset :
      ReusedOriginal.Construction.NeighborScan.activeTargets
        (target x) (setFlag A) (offset x (rep b))
        (offset x (rep b + 1)) = RS := by
    exact activeTargets_eq_numericNeighborhood_inter hx A (rep b) hr
  have hBrange : BS ⊆ Finset.range n := by
    exact (Finset.inter_subset_right).trans hA
  have hRrange : RS ⊆ Finset.range n := by
    exact (Finset.inter_subset_right).trans hA
  have hσ₂n : σ₂.vars "n" = n := by
    rw [hkeepRVar "n" (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hσ₁n
  have hσ₂blen : σ₂.vars "repairBLen" = BS.card := by
    rw [hkeepRVar "repairBLen" (by decide) (by decide) (by decide)
      (by decide) (by decide), hblen₁, hBset]
  have hσ₂bm : σ₂.arrs "repairBMarks" = arrOf n bm := by
    rw [hkeepR "repairBMarks" (by decide) (by decide)]
    exact hbm₁
  have hσ₂bl : σ₂.arrs "repairBList" = arrOf n bl := by
    rw [hkeepR "repairBList" (by decide) (by decide)]
    exact hbl₁
  have hσ₂domain : σ₂.arrs "drawDomain" = arrOf n domain := by
    rw [hkeepR "drawDomain" (by decide) (by decide),
      hkeepB "drawDomain" (by decide) (by decide), hσ₀arr]
    exact hdomain
  obtain ⟨σ₃, domain', rfilter, hdomain₃, henumX, hcountX, _hXrange,
    hbl₃, hrl₃, hbm₃, hrm₃, hblen₃, hrlen₃, hn₃,
    hframeArr₃, _hframeVar₃, _hinp₃, _hout₃⟩ :=
    appendSymmetricDifference_run
      hσ₂n hσ₂blen (by rw [hrlen₂, hRset])
      hσ₂bl hrl₂ hσ₂bm hrm₂ hσ₂domain
      (by simpa [hBset] using henumB)
      (by simpa [hRset] using henumR)
      hBrange hRrange
      hboundB hboundR
      (by simpa [hBset] using hmemB)
      (by simpa [hRset] using hmemR)
      (by omega) honeB
  have rcore : Run B repairDomainCore σ σ₃
      (54 * ((offset x (b + 1) - offset x b) +
          (offset x (rep b + 1) - offset x (rep b))) +
        24 * (BS.card + RS.card) + 61) := by
    have hseq := rrep.seq (rB.seq (rR.seq rfilter))
    have hbound : 3 + ((54 * (offset x (b + 1) - offset x b) + 22) +
        ((54 * (offset x (rep b + 1) - offset x (rep b)) + 22) +
          (24 * (BS.card + RS.card) + 14))) ≤
      54 * ((offset x (b + 1) - offset x b) +
        (offset x (rep b + 1) - offset x (rep b))) +
        24 * (BS.card + RS.card) + 61 := by omega
    simpa [repairDomainCore, collectRepairBAt, collectRepairRAt,
      ρB, ρR, hBset, hRset, seqs] using hseq.mono hbound
  refine ⟨σ₃, domain', bm, rm, bl, rl, ?_, hdomain₃, ?_, ?_,
    hbm₃, hrm₃, hbl₃, hrl₃, ?_, ?_, ?_, ?_, hboundB, hboundR,
    ?_, ?_, ?_, ?_, hn₃, ?_, ?_⟩
  · simpa [BS, RS] using rcore
  · simpa [BS, RS] using hcountX
  · simpa [BS, RS] using henumX
  · simpa [BS] using hblen₃
  · simpa [RS] using hrlen₃
  · simpa [hBset, BS] using hmemB
  · simpa [hRset, RS] using hmemR
  · simpa [hBset, BS] using henumB
  · simpa [hRset, RS] using henumR
  · rw [hframeArr₃ "repB" (by decide),
      hkeepR "repB" (by decide) (by decide),
      hkeepB "repB" (by decide) (by decide), hσ₀arr]
    exact hrep
  · rw [hframeArr₃ "activeA" (by decide),
      hkeepR "activeA" (by decide) (by decide),
      hkeepB "activeA" (by decide) (by decide), hσ₀arr]
    exact hactive
  · exact rcore.frame_inp (by
      simp [repairDomainCore, collectRepairBAt, collectRepairRAt,
        collectNeighborhoodAt, prepareNeighborAt, appendSymmetricDifference,
        appendBOnly, appendROnly, appendFiltered, appendFilteredBody,
        renameCom, collectNeighborBody, seqs, inc, Com.reads])
  · exact rcore.out_eq (by
      simp [repairDomainCore, collectRepairBAt, collectRepairRAt,
        collectNeighborhoodAt, prepareNeighborAt, appendSymmetricDifference,
        appendBOnly, appendROnly, appendFiltered, appendFilteredBody,
        renameCom, collectNeighborBody, seqs, inc, Com.NoWrite])

/-- Fixed local-repair draw builder. The private marks are cleared by
walking their own collected lists, so the source can run again for the next
exception with no full-vertex scratch reset. -/
def repairDomainSource : Com :=
  seqs [repairDomainCore, clearRepairBMarks, clearRepairRMarks]

lemma repairDomainSource_run
    {B n targetCap b : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    {A : Finset ℕ} {rep blist rlist domain : ℕ → ℕ} {σ : Env}
    (hx : EncodesGraph x n G)
    (htargetCap : targetCap = 2 * edgeCount x)
    (hA : A ⊆ Finset.range n)
    (hn : σ.vars "n" = n)
    (hbvar : σ.vars "repairB" = b)
    (hrep : σ.arrs "repB" = arrOf n rep)
    (hoff : σ.arrs "off" = arrOf (n + 1) (offset x))
    (htarget : σ.arrs "tgt" = arrOf targetCap (target x))
    (hactive : σ.arrs "activeA" = arrOf n (setFlag A))
    (hbmarks : σ.arrs "repairBMarks" = arrOf n (fun _ => 0))
    (hrmarks : σ.arrs "repairRMarks" = arrOf n (fun _ => 0))
    (hblist : σ.arrs "repairBList" = arrOf n blist)
    (hrlist : σ.arrs "repairRList" = arrOf n rlist)
    (hdomain : σ.arrs "drawDomain" = arrOf n domain)
    (hb : b < n) (hr : rep b < n)
    (hn1B : n + 1 < B) (htargetCapB : targetCap < B) :
    ∃ σ' domain' blist' rlist',
      Run B repairDomainSource σ σ'
        (54 * ((offset x (b + 1) - offset x b) +
            (offset x (rep b + 1) - offset x (rep b))) +
          36 * (((numericNeighborhood G b ∩ A).card) +
            ((numericNeighborhood G (rep b) ∩ A).card)) + 73) ∧
      σ'.arrs "drawDomain" = arrOf n domain' ∧
      σ'.vars "drawModulus" =
        ((numericNeighborhood G b ∩ A) ∆
          (numericNeighborhood G (rep b) ∩ A)).card ∧
      PrefixEnumerates (σ'.vars "drawModulus") domain'
        ((numericNeighborhood G b ∩ A) ∆
          (numericNeighborhood G (rep b) ∩ A)) ∧
      ((numericNeighborhood G b ∩ A) ∆
          (numericNeighborhood G (rep b) ∩ A)) ⊆ Finset.range n ∧
      σ'.arrs "repairBMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "repairRMarks" = arrOf n (fun _ => 0) ∧
      σ'.arrs "repairBList" = arrOf n blist' ∧
      σ'.arrs "repairRList" = arrOf n rlist' ∧
      σ'.vars "repairBLen" = (numericNeighborhood G b ∩ A).card ∧
      σ'.vars "repairRLen" = (numericNeighborhood G (rep b) ∩ A).card ∧
      σ'.arrs "repB" = arrOf n rep ∧
      σ'.arrs "activeA" = arrOf n (setFlag A) ∧
      σ'.arrs "off" = arrOf (n + 1) (offset x) ∧
      σ'.arrs "tgt" = arrOf targetCap (target x) ∧
      σ'.arrs "sampleFlags" = σ.arrs "sampleFlags" ∧
      σ'.arrs "classB" = σ.arrs "classB" ∧
      σ'.arrs "classSize" = σ.arrs "classSize" ∧
      σ'.arrs "ord" = σ.arrs "ord" ∧
      σ'.arrs "stamp" = σ.arrs "stamp" ∧
      σ'.arrs "activeB" = σ.arrs "activeB" ∧
      σ'.arrs "exceptionFlags" = σ.arrs "exceptionFlags" ∧
      σ'.vars "sampleCount" = σ.vars "sampleCount" ∧
      σ'.vars "n" = n ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let BS := numericNeighborhood G b ∩ A
  let RS := numericNeighborhood G (rep b) ∩ A
  obtain ⟨σ₁, out, bm, rm, bl, rl, rcore, hout, hcount, henumX,
    hbm, hrm, hbl, hrl, hblen, hrlen, hbmem, hrmem, hb01, hr01,
    hbenum, hrenum, _hrep₁, _hactive₁, hn₁, _hinp₁, _hout₁⟩ :=
    repairDomainCore_run hx htargetCap hA hn hbvar hrep hoff htarget
      hactive hbmarks hrmarks hblist hrlist hdomain hb hr hn1B htargetCapB
  have hBrange : BS ⊆ Finset.range n :=
    (Finset.inter_subset_right).trans hA
  have hRrange : RS ⊆ Finset.range n :=
    (Finset.inter_subset_right).trans hA
  let ρB := repairClearNames "repairBMarks" "repairBList" "repairBLen"
  let ρR := repairClearNames "repairRMarks" "repairRList" "repairRLen"
  obtain ⟨σ₂, rclearB, hzeroB, _hcursorB, _hinpB, _houtB⟩ :=
    clearNeighborhoodSupport_run (B := B) (n := n) (h := BS.card)
      (S := BS) (marks := bm) (list := bl) (σ := σ₁)
      ρB "repairBMarks" "repairBList"
      "repairBLen" (by decide) (by decide) (by decide)
      (by decide) (by decide) hn₁ hblen hbm hbl hbenum hBrange
      hb01 hbmem (by omega)
  have hσ₂n : σ₂.vars "n" = n := by
    rw [rclearB.frame_var "n" (by decide)]
    exact hn₁
  have hσ₂rlen : σ₂.vars "repairRLen" = RS.card := by
    rw [rclearB.frame_var "repairRLen" (by decide)]
    exact hrlen
  have hσ₂rm : σ₂.arrs "repairRMarks" = arrOf n rm := by
    rw [rclearB.frame_arr "repairRMarks" (by decide)]
    exact hrm
  have hσ₂rl : σ₂.arrs "repairRList" = arrOf n rl := by
    rw [rclearB.frame_arr "repairRList" (by decide)]
    exact hrl
  obtain ⟨σ₃, rclearR, hzeroR, _hcursorR, _hinpR, _houtR⟩ :=
    clearNeighborhoodSupport_run (B := B) (n := n) (h := RS.card)
      (S := RS) (marks := rm) (list := rl) (σ := σ₂)
      ρR "repairRMarks" "repairRList"
      "repairRLen" (by decide) (by decide) (by decide)
      (by decide) (by decide) hσ₂n hσ₂rlen hσ₂rm hσ₂rl hrenum hRrange
      hr01 hrmem (by omega)
  have rfinal : Run B repairDomainSource σ σ₃
      (54 * ((offset x (b + 1) - offset x b) +
          (offset x (rep b + 1) - offset x (rep b))) +
        36 * (BS.card + RS.card) + 73) := by
    have hseq := rcore.seq (rclearB.seq rclearR)
    have hbound :
        (54 * ((offset x (b + 1) - offset x b) +
            (offset x (rep b + 1) - offset x (rep b))) +
          24 * (BS.card + RS.card) + 61) +
          ((12 * BS.card + 6) + (12 * RS.card + 6)) ≤
        54 * ((offset x (b + 1) - offset x b) +
          (offset x (rep b + 1) - offset x (rep b))) +
          36 * (BS.card + RS.card) + 73 := by omega
    simpa [repairDomainSource, ρB, ρR, clearRepairBMarks,
      clearRepairRMarks, BS, RS, seqs] using hseq.mono hbound
  have hfinalDomain : σ₃.arrs "drawDomain" = arrOf n out := by
    rw [rclearR.frame_arr "drawDomain" (by decide),
      rclearB.frame_arr "drawDomain" (by decide)]
    exact hout
  have hfinalCount : σ₃.vars "drawModulus" = (BS ∆ RS).card := by
    rw [rclearR.frame_var "drawModulus" (by decide),
      rclearB.frame_var "drawModulus" (by decide)]
    exact hcount
  have hfinalBZero : σ₃.arrs "repairBMarks" = arrOf n (fun _ => 0) := by
    rw [rclearR.frame_arr "repairBMarks" (by decide)]
    exact hzeroB
  have hXrange : BS ∆ RS ⊆ Finset.range n := by
    rw [Finset.symmDiff_def]
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact hBrange (Finset.mem_sdiff.mp hv).1
    · exact hRrange (Finset.mem_sdiff.mp hv).1
  refine ⟨σ₃, out, bl, rl, ?_, hfinalDomain, ?_, ?_, ?_, hfinalBZero,
    hzeroR, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [BS, RS] using rfinal
  · simpa [BS, RS] using hfinalCount
  · rw [rclearR.frame_var "drawModulus" (by decide),
      rclearB.frame_var "drawModulus" (by decide)]
    simpa [BS, RS] using henumX
  · simpa [BS, RS] using hXrange
  · rw [rclearR.frame_arr "repairBList" (by decide),
      rclearB.frame_arr "repairBList" (by decide)]
    exact hbl
  · rw [rclearR.frame_arr "repairRList" (by decide),
      rclearB.frame_arr "repairRList" (by decide)]
    exact hrl
  · rw [rclearR.frame_var "repairBLen" (by decide),
      rclearB.frame_var "repairBLen" (by decide)]
    exact hblen
  · rw [rclearR.frame_var "repairRLen" (by decide),
      rclearB.frame_var "repairRLen" (by decide)]
    exact hrlen
  · exact (rfinal.frame_arr "repB" (by decide)).trans hrep
  · exact (rfinal.frame_arr "activeA" (by decide)).trans hactive
  · exact (rfinal.frame_arr "off" (by decide)).trans hoff
  · exact (rfinal.frame_arr "tgt" (by decide)).trans htarget
  · exact rfinal.frame_arr "sampleFlags" (by decide)
  · exact rfinal.frame_arr "classB" (by decide)
  · exact rfinal.frame_arr "classSize" (by decide)
  · exact rfinal.frame_arr "ord" (by decide)
  · exact rfinal.frame_arr "stamp" (by decide)
  · exact rfinal.frame_arr "activeB" (by decide)
  · exact rfinal.frame_arr "exceptionFlags" (by decide)
  · exact rfinal.frame_var "sampleCount" (by decide)
  · rw [rclearR.frame_var "n" (by decide),
      rclearB.frame_var "n" (by decide)]
    exact hn₁
  · exact rfinal.frame_inp (by decide)
  · exact rfinal.out_eq (by decide)

/-- The exact source budget is bounded only by the two CSR degrees. Duplicate
targets can only decrease the two distinct-neighbor counts. -/
lemma repairDomainSource_cost_le
    {n b : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) (A : Finset ℕ)
    (rep : ℕ → ℕ) (hb : b < n) (hr : rep b < n) :
    54 * ((offset x (b + 1) - offset x b) +
        (offset x (rep b + 1) - offset x (rep b))) +
      36 * (((numericNeighborhood G b ∩ A).card) +
        ((numericNeighborhood G (rep b) ∩ A).card)) + 73 ≤
    90 * ((offset x (b + 1) - offset x b) +
      (offset x (rep b + 1) - offset x (rep b))) + 73 := by
  have hbcard : (numericNeighborhood G b ∩ A).card ≤
      offset x (b + 1) - offset x b := by
    rw [← activeTargets_eq_numericNeighborhood_inter hx A b hb]
    exact card_activeTargets_le_interval
  have hrcard : (numericNeighborhood G (rep b) ∩ A).card ≤
      offset x (rep b + 1) - offset x (rep b) := by
    rw [← activeTargets_eq_numericNeighborhood_inter hx A (rep b) hr]
    exact card_activeTargets_le_interval
  omega

end

end Lax457868Proofs.RepairFilterSource
