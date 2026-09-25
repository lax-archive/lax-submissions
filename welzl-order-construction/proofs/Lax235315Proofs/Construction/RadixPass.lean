import Lax235315Proofs.Construction.RadixMath
import Lax235315Proofs.Construction.WelzlStraight
import Mathlib.Tactic

/-! Source-level correctness of the stable counting-sort pass. -/

namespace Lax235315Proofs.Construction.RadixPass

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlStraight

private theorem getD_eq_of_cells {n : ℕ} {f : ℕ → ℕ} {xs : List ℕ}
    {i : ℕ} (harr : i < n) (hixs : i < xs.length)
    (hf : ∀ j < xs.length, f j = xs.getD j 0) :
    (arrOf n f).getD i 0 = xs.getD i 0 := by
  rw [getD_arrOf f harr, hf i hixs]

private theorem count_update (key : ℕ → ℕ) (xs : List ℕ)
    {i : ℕ} (hi : i < xs.length) :
    upd (fun d => countDigit key (xs.take i) d) (key xs[i])
        (countDigit key (xs.take i) (key xs[i]) + 1) =
      fun d => countDigit key (xs.take (i + 1)) d := by
  funext d
  rw [countDigit_take_succ key xs hi]
  by_cases hd : d = key xs[i]
  · subst d
    simp [upd]
  · have hne : key xs[i] ≠ d := Ne.symm hd
    simp [upd, hd, hne]

/-- Exact invariant of the counting phase. -/
def CountInv (n q : ℕ) (xs : List ℕ) (keyName : String)
    (key ord : ℕ → ℕ)
    (τ : Env) : Prop :=
  τ.vars "i" ≤ xs.length ∧ τ.vars "alen" = xs.length ∧
    τ.vars "qpow" = q ∧
    τ.arrs "ord" = arrOf n ord ∧
    (∀ j < xs.length, ord j = xs.getD j 0) ∧
    τ.arrs keyName = arrOf n key ∧
    τ.arrs "count" = arrOf q
      (fun d => countDigit key (xs.take (τ.vars "i")) d)

private theorem count_body_spec {B n q : ℕ} {xs : List ℕ}
    {keyName : String} {key ord : ℕ → ℕ}
    (hkeyCount : keyName ≠ "count")
    (hxn : xs.length ≤ n) (hnB : n < B) (hqB : q < B)
    (hvert : ∀ x ∈ xs, x < n) (hkey : ∀ x ∈ xs, key x < q) :
    Spec B
      (fun τ => CountInv n q xs keyName key ord τ ∧ τ.vars "i" < xs.length)
      (seqs [
        .assign "v" (.get "ord" (.var "i")),
        .assign "digit" (.get keyName (.var "v")),
        .store "count" (.var "digit")
          (.add (.get "count" (.var "digit")) (.lit 1)),
        inc "i"])
      (fun τ τ' => CountInv n q xs keyName key ord τ' ∧
        τ'.vars "i" = τ.vars "i" + 1)
      18 := by
  intro τ hτ
  rcases hτ with ⟨⟨hile, halen, hqpow, hord, hordval, hkeys, hcount⟩, hi⟩
  have hin : τ.vars "i" < n := hi.trans_le hxn
  have hiB : τ.vars "i" < B := hin.trans hnB
  have hxi : xs.getD (τ.vars "i") 0 = xs[τ.vars "i"] := by
    simp [List.getD_eq_getElem?_getD, hi]
  have hxmem : xs[τ.vars "i"] ∈ xs := List.getElem_mem hi
  have hxn : xs[τ.vars "i"] < n := hvert _ hxmem
  have hxB : xs[τ.vars "i"] < B := hxn.trans hnB
  have hordGet : (τ.arrs "ord")[τ.vars "i"]? = some xs[τ.vars "i"] := by
    rw [hord, getElem?_arrOf ord hin, hordval _ hi, hxi]
  have hordVal : (τ.arrs "ord")[τ.vars "i"]?.getD 0 =
      xs[τ.vars "i"] := by simp [hordGet]
  have hordGetD : (τ.arrs "ord").getD (τ.vars "i") 0 =
      xs[τ.vars "i"] := by
    rw [hord, getD_arrOf ord hin, hordval _ hi, hxi]
  have hordLen : (τ.arrs "ord").length = n := by simp [hord]
  have hkeyGet : (τ.arrs keyName)[xs[τ.vars "i"]]? =
      some (key xs[τ.vars "i"]) := by
    rw [hkeys, getElem?_arrOf key hxn]
  have hkeyVal : (τ.arrs keyName)[xs[τ.vars "i"]]?.getD 0 =
      key xs[τ.vars "i"] := by simp [hkeyGet]
  have hkeyGetD : (τ.arrs keyName).getD xs[τ.vars "i"] 0 =
      key xs[τ.vars "i"] := by
    rw [hkeys, getD_arrOf key hxn]
  have hkeyLen : (τ.arrs keyName).length = n := by simp [hkeys]
  have hdigitq : key xs[τ.vars "i"] < q := hkey _ hxmem
  have hdigitB : key xs[τ.vars "i"] < B := hdigitq.trans hqB
  have hcountGet : (τ.arrs "count")[key xs[τ.vars "i"]]? =
      some (countDigit key (xs.take (τ.vars "i"))
        (key xs[τ.vars "i"])) := by
    rw [hcount, getElem?_arrOf _ hdigitq]
  have hcountVal : (τ.arrs "count")[key xs[τ.vars "i"]]?.getD 0 =
      countDigit key (xs.take (τ.vars "i")) (key xs[τ.vars "i"]) := by
    simp [hcountGet]
  have hcountGetD : (τ.arrs "count").getD (key xs[τ.vars "i"]) 0 =
      countDigit key (xs.take (τ.vars "i")) (key xs[τ.vars "i"]) := by
    rw [hcount, getD_arrOf _ hdigitq]
  have hcountLe : countDigit key (xs.take (τ.vars "i"))
      (key xs[τ.vars "i"]) ≤ τ.vars "i" := by
    unfold countDigit
    exact (List.length_filter_le _ _).trans (List.length_take_le ..)
  have hcountSuccB : countDigit key (xs.take (τ.vars "i"))
      (key xs[τ.vars "i"]) + 1 < B := by omega
  have hiSuccB : τ.vars "i" + 1 < B := by omega
  have hcountLen : key xs[τ.vars "i"] < (τ.arrs "count").length := by
    rw [hcount, length_arrOf]
    exact hdigitq
  have hcountLength : (τ.arrs "count").length = q := by simp [hcount]
  run_vcg
  refine ⟨⟨?_, ?_, ?_, ?_, hordval, ?_, ?_⟩, by simp⟩
  · simp
    omega
  · simp [halen]
  · simp [hqpow]
  · simp [hord]
  · simp [hkeys, hkeyCount]
  · simp [hordVal, hkeyVal, hcountVal]
    rw [hcount, set_arrOf_eq_upd, count_update key xs hi]
  all_goals
    simp [hordVal, hkeyVal, hcountVal, hordLen, hkeyLen, hcountLength] <;>
      omega

/-- The first loop of a radix pass replaces the zeroed counter array by the
exact multiplicity of every digit. -/
theorem countPhase_run {B n q : ℕ} {xs : List ℕ} {keyName : String}
    {key ord count : ℕ → ℕ}
    {σ : Env}
    (halen : σ.vars "alen" = xs.length) (hqpow : σ.vars "qpow" = q)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hordval : ∀ i < xs.length, ord i = xs.getD i 0)
    (hkeys : σ.arrs keyName = arrOf n key)
    (hcount : σ.arrs "count" = arrOf q count)
    (hcount0 : ∀ d < q, count d = 0)
    (hxn : xs.length ≤ n) (hnB : n < B) (hqB : q < B)
    (hvert : ∀ x ∈ xs, x < n) (hkey : ∀ x ∈ xs, key x < q)
    (hkeyCount : keyName ≠ "count") :
    ∃ σ', Run B
        (seqs [
          .assign "i" (.lit 0),
          .while (.lt (.var "i") (.var "alen")) <|
            seqs [
              .assign "v" (.get "ord" (.var "i")),
              .assign "digit" (.get keyName (.var "v")),
              .store "count" (.var "digit")
                (.add (.get "count" (.var "digit")) (.lit 1)),
              inc "i"]])
        σ σ' (22 * xs.length + 6) ∧
      σ'.arrs "count" = arrOf q (fun d => countDigit key xs d) ∧
      σ'.vars "i" = xs.length := by
  have hI₀ : CountInv n q xs keyName key ord (σ.setVar "i" 0) := by
    refine ⟨by simp, by simp [halen], by simp [hqpow], by simp [hord],
      hordval, by simp [hkeys], ?_⟩
    simp only [arrs_setVar, vars_setVar, if_pos, List.take_zero]
    rw [hcount]
    apply arrOf_congr
    intro d hd
    simp [hcount, countDigit, hcount0 d hd]
  have hloop := Spec.forRangeZero (B := B) "i" "alen"
    (CountInv n q xs keyName key ord) xs.length 18
    (lt_of_le_of_lt hxn hnB)
    (fun _ h => h.1) (fun _ h => h.2.1)
    (count_body_spec hkeyCount hxn hnB hqB hvert hkey)
  obtain ⟨σ', rloop, hI', hi'⟩ := hloop.run hI₀
  refine ⟨σ', ?_, ?_, hi'⟩
  · simpa [seqs] using rloop
  · simpa [hi'] using hI'.2.2.2.2.2.2

/-! ### Prefix sums -/

def prefixCount (key : ℕ → ℕ) (xs : List ℕ) (processed d : ℕ) : ℕ :=
  if d < processed then startDigit key xs d else countDigit key xs d

@[simp] theorem prefixCount_zero (key : ℕ → ℕ) (xs : List ℕ) (d : ℕ) :
    prefixCount key xs 0 d = countDigit key xs d := by
  simp [prefixCount]

private theorem prefixCount_update (key : ℕ → ℕ) (xs : List ℕ)
    (i : ℕ) :
    upd (prefixCount key xs i) i (startDigit key xs i) =
      prefixCount key xs (i + 1) := by
  funext d
  by_cases hdi : d = i
  · subst d
    simp [upd, prefixCount]
  · by_cases hdlt : d < i
    · have : d < i + 1 := by omega
      simp [upd, prefixCount, hdi, hdlt, this]
    · have : ¬ d < i + 1 := by omega
      simp [upd, prefixCount, hdi, hdlt, this]

def PrefixInv (q : ℕ) (xs : List ℕ) (key : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "digit" ≤ q ∧ τ.vars "qpow" = q ∧
    τ.vars "sum" = startDigit key xs (τ.vars "digit") ∧
    τ.arrs "count" = arrOf q (prefixCount key xs (τ.vars "digit"))

private theorem prefix_body_spec {B q : ℕ} {xs : List ℕ} {key : ℕ → ℕ}
    (hqB : q < B) (hlenB : xs.length < B)
    (hstart : startDigit key xs q = xs.length) :
    Spec B
      (fun τ => PrefixInv q xs key τ ∧ τ.vars "digit" < q)
      (seqs [
        .assign "tmp" (.get "count" (.var "digit")),
        .store "count" (.var "digit") (.var "sum"),
        .assign "sum" (.add (.var "sum") (.var "tmp")),
        inc "digit"])
      (fun τ τ' => PrefixInv q xs key τ' ∧
        τ'.vars "digit" = τ.vars "digit" + 1)
      14 := by
  intro τ hτ
  rcases hτ with ⟨⟨hdle, hqpow, hsum, hcount⟩, hdq⟩
  have hdB : τ.vars "digit" < B := hdq.trans hqB
  have hcountLen : (τ.arrs "count").length = q := by simp [hcount]
  have hcell : (τ.arrs "count")[τ.vars "digit"]?.getD 0 =
      countDigit key xs (τ.vars "digit") := by
    rw [hcount, getElem?_arrOf _ hdq]
    simp [prefixCount]
  have hstartLe : startDigit key xs (τ.vars "digit") ≤ xs.length := by
    rw [← hstart]
    exact startDigit_mono key xs hdle
  have hnextLe : startDigit key xs (τ.vars "digit" + 1) ≤ xs.length := by
    rw [← hstart]
    exact startDigit_mono key xs (by omega)
  have hsumB : τ.vars "sum" < B := by omega
  have htmpB : countDigit key xs (τ.vars "digit") < B := by
    have hle : countDigit key xs (τ.vars "digit") ≤ xs.length := by
      exact List.length_filter_le _ _
    omega
  have hnewSumB : startDigit key xs (τ.vars "digit") +
      countDigit key xs (τ.vars "digit") < B := by
    rw [← startDigit_succ]
    omega
  have hdSuccB : τ.vars "digit" + 1 < B := by omega
  run_vcg
  refine ⟨⟨by simp; omega, by simp [hqpow], ?_, ?_⟩, by simp⟩
  · simp [hcell, hsum, startDigit_succ]
  · simp [hcell, hsum, hcount, set_arrOf_eq_upd, prefixCount_update]
  all_goals simp [hcell, hcountLen] <;> omega

theorem prefixPhase_run {B q : ℕ} {xs : List ℕ} {key count : ℕ → ℕ}
    {σ : Env}
    (hqpow : σ.vars "qpow" = q)
    (hcount : σ.arrs "count" = arrOf q count)
    (hcountval : ∀ d < q, count d = countDigit key xs d)
    (hqB : q < B) (hlenB : xs.length < B)
    (hstart : startDigit key xs q = xs.length) :
    ∃ σ', Run B
        (seqs [
          .assign "sum" (.lit 0),
          .assign "digit" (.lit 0),
          .while (.lt (.var "digit") (.var "qpow")) <|
            seqs [
              .assign "tmp" (.get "count" (.var "digit")),
              .store "count" (.var "digit") (.var "sum"),
              .assign "sum" (.add (.var "sum") (.var "tmp")),
              inc "digit"]])
        σ σ' (18 * q + 8) ∧
      σ'.arrs "count" = arrOf q (startDigit key xs) ∧
      σ'.vars "digit" = q := by
  let σ₀ := σ.setVar "sum" 0
  have r₀ : Run B (.assign "sum" (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  have hI₀ : PrefixInv q xs key (σ₀.setVar "digit" 0) := by
    refine ⟨by simp [σ₀], by simp [σ₀, hqpow], by simp [σ₀], ?_⟩
    simp only [σ₀, arrs_setVar]
    rw [hcount]
    apply arrOf_congr
    intro d hd
    simp [prefixCount, hcountval d hd]
  have hloop := Spec.forRangeZero (B := B) "digit" "qpow"
    (PrefixInv q xs key) q 14 hqB
    (fun _ h => h.1) (fun _ h => h.2.1)
    (prefix_body_spec hqB hlenB hstart)
  obtain ⟨σ', rloop, hI', hd'⟩ := hloop.run hI₀
  refine ⟨σ', ?_, ?_, hd'⟩
  · simpa [seqs] using (r₀.seq rloop).mono (by omega)
  · have harr := hI'.2.2.2
    rw [hd'] at harr
    rw [harr]
    apply arrOf_congr
    intro d hd
    simp [prefixCount, hd]

/-! ### Stable scatter -/

def scatterCount (key : ℕ → ℕ) (xs : List ℕ) (processed d : ℕ) : ℕ :=
  startDigit key xs d + countDigit key (xs.take processed) d

private theorem scatterCount_update (key : ℕ → ℕ) (xs : List ℕ)
    {i : ℕ} (hi : i < xs.length) :
    upd (scatterCount key xs i) (key xs[i])
        (scatterCount key xs i (key xs[i]) + 1) =
      scatterCount key xs (i + 1) := by
  funext d
  simp only [scatterCount, countDigit_take_succ key xs hi]
  by_cases hd : d = key xs[i]
  · subst d
    simp [upd]
    omega
  · have hne : key xs[i] ≠ d := Ne.symm hd
    simp [upd, hd, hne]
    rfl

private theorem scatterPrefix_update (key : ℕ → ℕ) (xs : List ℕ)
    (initial : ℕ → ℕ) {i : ℕ} (hi : i < xs.length) :
    upd (scatterPrefix key xs initial i)
        (scatterCount key xs i (key xs[i])) xs[i] =
      scatterPrefix key xs initial (i + 1) := by
  rw [scatterPrefix]
  simp only [List.getD_eq_getElem _ _ hi]
  rfl

def ScatterInv (n q : ℕ) (xs : List ℕ) (keyName : String)
    (key ord initial : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "i" ≤ xs.length ∧ τ.vars "alen" = xs.length ∧
    τ.arrs "ord" = arrOf n ord ∧
    (∀ j < xs.length, ord j = xs.getD j 0) ∧
    τ.arrs keyName = arrOf n key ∧
    τ.arrs "count" = arrOf q (scatterCount key xs (τ.vars "i")) ∧
    τ.arrs "scratchOrder" =
      arrOf n (scatterPrefix key xs initial (τ.vars "i"))

private theorem scatter_body_spec {B n q : ℕ} {xs : List ℕ}
    {keyName : String} {key ord initial : ℕ → ℕ}
    (hkeyCount : keyName ≠ "count")
    (hkeyScratch : keyName ≠ "scratchOrder")
    (hordCount : "ord" ≠ "count")
    (hordScratch : "ord" ≠ "scratchOrder")
    (hcountScratch : "count" ≠ "scratchOrder")
    (hxn : xs.length ≤ n) (hnB : n < B) (hqB : q < B)
    (hvert : ∀ x ∈ xs, x < n) (hkey : ∀ x ∈ xs, key x < q)
    (hstart : startDigit key xs q = xs.length) :
    Spec B
      (fun τ => ScatterInv n q xs keyName key ord initial τ ∧
        τ.vars "i" < xs.length)
      (seqs [
        .assign "v" (.get "ord" (.var "i")),
        .assign "digit" (.get keyName (.var "v")),
        .assign "pos" (.get "count" (.var "digit")),
        .store "scratchOrder" (.var "pos") (.var "v"),
        .store "count" (.var "digit") (.add (.var "pos") (.lit 1)),
        inc "i"])
      (fun τ τ' => ScatterInv n q xs keyName key ord initial τ' ∧
        τ'.vars "i" = τ.vars "i" + 1)
      24 := by
  intro τ hτ
  rcases hτ with ⟨⟨hile, halen, hord, hordval, hkeys, hcount, hscratch⟩, hi⟩
  have hin : τ.vars "i" < n := hi.trans_le hxn
  have hiB : τ.vars "i" < B := hin.trans hnB
  have hxi : xs.getD (τ.vars "i") 0 = xs[τ.vars "i"] := by
    simp [List.getD_eq_getElem?_getD, hi]
  have hxmem : xs[τ.vars "i"] ∈ xs := List.getElem_mem hi
  have hxN : xs[τ.vars "i"] < n := hvert _ hxmem
  have hxB : xs[τ.vars "i"] < B := hxN.trans hnB
  have hordVal : (τ.arrs "ord")[τ.vars "i"]?.getD 0 = xs[τ.vars "i"] := by
    rw [hord, getElem?_arrOf ord hin, hordval _ hi, hxi]
    rfl
  have hordLen : (τ.arrs "ord").length = n := by simp [hord]
  have hdq : key xs[τ.vars "i"] < q := hkey _ hxmem
  have hdB : key xs[τ.vars "i"] < B := hdq.trans hqB
  have hkeyVal : (τ.arrs keyName)[xs[τ.vars "i"]]?.getD 0 =
      key xs[τ.vars "i"] := by
    rw [hkeys, getElem?_arrOf key hxN]
    rfl
  have hkeyLen : (τ.arrs keyName).length = n := by simp [hkeys]
  let pos := scatterCount key xs (τ.vars "i") (key xs[τ.vars "i"])
  have hcountVal : (τ.arrs "count")[key xs[τ.vars "i"]]?.getD 0 = pos := by
    rw [hcount, getElem?_arrOf _ hdq]
    rfl
  have hcountLen : (τ.arrs "count").length = q := by simp [hcount]
  have hprefixStrict : countDigit key (xs.take (τ.vars "i"))
      (key xs[τ.vars "i"]) < countDigit key xs (key xs[τ.vars "i"]) := by
    have hs : countDigit key (xs.take (τ.vars "i" + 1))
        (key xs[τ.vars "i"]) = countDigit key (xs.take (τ.vars "i"))
          (key xs[τ.vars "i"]) + 1 := by
      simpa using countDigit_take_succ key xs hi (key xs[τ.vars "i"])
    have hle := countDigit_take_le key xs (τ.vars "i" + 1)
      (key xs[τ.vars "i"])
    omega
  have hinter := digit_intervals_separated key xs hdq
  have hposLen : pos < xs.length := by
    dsimp [pos, scatterCount]
    rw [← hstart]
    omega
  have hposN : pos < n := hposLen.trans_le hxn
  have hposB : pos < B := hposN.trans hnB
  have hposSuccB : pos + 1 < B := by omega
  have hscratchLen : (τ.arrs "scratchOrder").length = n := by simp [hscratch]
  have hiSuccB : τ.vars "i" + 1 < B := by omega
  run_vcg
  refine ⟨⟨by simp; omega, by simp [halen], ?_, hordval, ?_, ?_, ?_⟩, by simp⟩
  · simp [hord, hordScratch, hordCount]
  · simp [hkeys, hkeyCount, hkeyScratch]
  · simp [hordVal, hkeyVal, hcountVal, pos, hcountScratch]
    rw [hcount, set_arrOf_eq_upd, scatterCount_update key xs hi]
  · simp [hordVal, hkeyVal, hcountVal, pos, hcountScratch]
    rw [hscratch, set_arrOf_eq_upd, scatterPrefix_update key xs initial hi]
  all_goals
    simp [hordVal, hkeyVal, hcountVal, hordLen, hkeyLen, hcountLen,
      hscratchLen] <;> omega

theorem scatterPhase_run {B n q : ℕ} {xs : List ℕ} {keyName : String}
    {key ord count scratch : ℕ → ℕ} {σ : Env}
    (halen : σ.vars "alen" = xs.length)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hordval : ∀ i < xs.length, ord i = xs.getD i 0)
    (hkeys : σ.arrs keyName = arrOf n key)
    (hcount : σ.arrs "count" = arrOf q count)
    (hcountval : ∀ d < q, count d = startDigit key xs d)
    (hscratch : σ.arrs "scratchOrder" = arrOf n scratch)
    (hkeyCount : keyName ≠ "count")
    (hkeyScratch : keyName ≠ "scratchOrder")
    (hxn : xs.length ≤ n) (hnB : n < B) (hqB : q < B)
    (hxs : xs.Nodup)
    (hvert : ∀ x ∈ xs, x < n) (hkey : ∀ x ∈ xs, key x < q)
    (hstart : startDigit key xs q = xs.length) :
    ∃ σ' scratch', Run B
        (seqs [
          .assign "i" (.lit 0),
          .while (.lt (.var "i") (.var "alen")) <|
            seqs [
              .assign "v" (.get "ord" (.var "i")),
              .assign "digit" (.get keyName (.var "v")),
              .assign "pos" (.get "count" (.var "digit")),
              .store "scratchOrder" (.var "pos") (.var "v"),
              .store "count" (.var "digit") (.add (.var "pos") (.lit 1)),
              inc "i"]])
        σ σ' (28 * xs.length + 6) ∧
      σ'.arrs "scratchOrder" = arrOf n scratch' ∧
      (∀ i < xs.length, scratch' i = (bucketSort q key xs).getD i 0) ∧
      σ'.vars "i" = xs.length := by
  have hI₀ : ScatterInv n q xs keyName key ord scratch (σ.setVar "i" 0) := by
    refine ⟨by simp, by simp [halen], by simp [hord], hordval, by simp [hkeys], ?_,
      by simp [hscratch, scatterPrefix]⟩
    simp only [arrs_setVar, vars_setVar, if_pos]
    rw [hcount]
    apply arrOf_congr
    intro d hd
    simp [scatterCount, countDigit, hcountval d hd]
  have hloop := Spec.forRangeZero (B := B) "i" "alen"
    (ScatterInv n q xs keyName key ord scratch) xs.length 24
    (lt_of_le_of_lt hxn hnB)
    (fun _ h => h.1) (fun _ h => h.2.1)
    (scatter_body_spec hkeyCount hkeyScratch (by decide) (by decide) (by decide)
      hxn hnB hqB hvert hkey hstart)
  obtain ⟨σ', rloop, hI', hi'⟩ := hloop.run hI₀
  let scratch' := scatterPrefix key xs scratch xs.length
  refine ⟨σ', scratch', by simpa [seqs] using rloop, ?_, ?_, hi'⟩
  · simpa [scratch', hi'] using hI'.2.2.2.2.2.2
  · intro i hi
    dsimp [scratch']
    exact scatterPrefix_eq_bucketSort key xs scratch hxs hkey hi

/-! ### Copying the stable output back -/

def CopyInv (n : ℕ) (ys : List ℕ) (scratch : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "i" ≤ ys.length ∧ τ.vars "alen" = ys.length ∧
    τ.arrs "scratchOrder" = arrOf n scratch ∧
    (∀ j < ys.length, scratch j = ys.getD j 0) ∧
    Fill.Below "ord" "i" n (fun j => ys.getD j 0) τ

private theorem copy_body_spec {B n : ℕ} {ys : List ℕ} {scratch : ℕ → ℕ}
    (hylen : ys.length ≤ n) (hnB : n < B)
    (hyB : ∀ y ∈ ys, y < B) :
    Spec B
      (fun τ => CopyInv n ys scratch τ ∧ τ.vars "i" < ys.length)
      (seqs [
        .store "ord" (.var "i") (.get "scratchOrder" (.var "i")),
        inc "i"])
      (fun τ τ' => CopyInv n ys scratch τ' ∧
        τ'.vars "i" = τ.vars "i" + 1)
      8 := by
  intro τ hτ
  rcases hτ with ⟨⟨hile, halen, hscratch, hscratchval, hfill⟩, hi⟩
  have hin : τ.vars "i" < n := hi.trans_le hylen
  have hiB : τ.vars "i" < B := hin.trans hnB
  have hscratchLen : (τ.arrs "scratchOrder").length = n := by simp [hscratch]
  have hcell : (τ.arrs "scratchOrder")[τ.vars "i"]?.getD 0 =
      ys.getD (τ.vars "i") 0 := by
    rw [hscratch, getElem?_arrOf scratch hin, hscratchval _ hi]
    rfl
  have hcellB : ys.getD (τ.vars "i") 0 < B := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact hyB _ (List.getElem_mem hi)
  have hiSuccB : τ.vars "i" + 1 < B := by omega
  have hordLen : (τ.arrs "ord").length = n := hfill.length
  run_vcg
  refine ⟨⟨by simp; omega, by simp [halen], by simp [hscratch], hscratchval, ?_⟩,
    by simp⟩
  · exact hfill.step hin (by simpa [hcell])
  all_goals simp [hcell, hscratchLen, hordLen] <;> omega

theorem copyPhase_run {B n : ℕ} {ys : List ℕ} {scratch ord : ℕ → ℕ}
    {σ : Env}
    (halen : σ.vars "alen" = ys.length)
    (hscratch : σ.arrs "scratchOrder" = arrOf n scratch)
    (hscratchval : ∀ i < ys.length, scratch i = ys.getD i 0)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hylen : ys.length ≤ n) (hnB : n < B)
    (hyB : ∀ y ∈ ys, y < B) :
    ∃ σ' ord', Run B
        (seqs [
          .assign "i" (.lit 0),
          .while (.lt (.var "i") (.var "alen")) <|
            seqs [
              .store "ord" (.var "i") (.get "scratchOrder" (.var "i")),
              inc "i"]])
        σ σ' (12 * ys.length + 6) ∧
      σ'.arrs "ord" = arrOf n ord' ∧
      (∀ i < ys.length, ord' i = ys.getD i 0) ∧
      σ'.vars "i" = ys.length := by
  have hI₀ : CopyInv n ys scratch (σ.setVar "i" 0) := by
    refine ⟨by simp, by simp [halen], by simp [hscratch], hscratchval, ?_⟩
    exact Fill.below_zero (g := ord) (by simp [hord]) (by simp)
  have hloop := Spec.forRangeZero (B := B) "i" "alen"
    (CopyInv n ys scratch) ys.length 8 (lt_of_le_of_lt hylen hnB)
    (fun _ h => h.1) (fun _ h => h.2.1)
    (copy_body_spec hylen hnB hyB)
  obtain ⟨σ', rloop, hI', hi'⟩ := hloop.run hI₀
  obtain ⟨ord', hfill⟩ := hI'.2.2.2.2
  refine ⟨σ', ord', by simpa [seqs] using rloop, hfill.arr, ?_, hi'⟩
  intro i hi
  exact hfill.cell (by simpa [hi'] using hi)

/-! ### The complete pass -/

/-- One concrete counting-sort pass realizes the mathematical stable bucket
sort, with a linear source cost. -/
theorem radixPass_run {B n q : ℕ} {xs : List ℕ} {keyName : String}
    {key ord count scratch : ℕ → ℕ} {σ : Env}
    (halen : σ.vars "alen" = xs.length) (hqpow : σ.vars "qpow" = q)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hordval : ∀ i < xs.length, ord i = xs.getD i 0)
    (hkeys : σ.arrs keyName = arrOf n key)
    (hcount : σ.arrs "count" = arrOf q count)
    (hscratch : σ.arrs "scratchOrder" = arrOf n scratch)
    (hkeyOrd : keyName ≠ "ord") (hkeyCount : keyName ≠ "count")
    (hkeyScratch : keyName ≠ "scratchOrder")
    (hxn : xs.length ≤ n) (hnB : n < B) (hqB : q < B)
    (hxs : xs.Nodup)
    (hvert : ∀ x ∈ xs, x < n) (hkey : ∀ x ∈ xs, key x < q) :
    ∃ σ' ord', Run B (radixPass keyName) σ σ'
        (64 * (xs.length + q + 1)) ∧
      σ'.vars "alen" = xs.length ∧ σ'.vars "qpow" = q ∧
      σ'.arrs "ord" = arrOf n ord' ∧
      (∀ i < xs.length, ord' i = (bucketSort q key xs).getD i 0) ∧
      σ'.arrs keyName = arrOf n key := by
  have hstart : startDigit key xs q = xs.length := by
    rw [← length_bucketSort_eq_startDigit]
    exact (bucketSort_perm hxs hkey).length_eq
  obtain ⟨σ₁, count₁, r₁, hcount₁, hzero₁⟩ :=
    clearArray_run hcount hqpow (by decide) hqB
  have halen₁ : σ₁.vars "alen" = xs.length := by
    rw [r₁.frame_var "alen" (by simp [clearArray, seqs, inc, Com.wvars])]
    exact halen
  have hqpow₁ : σ₁.vars "qpow" = q := by
    rw [r₁.frame_var "qpow" (by simp [clearArray, seqs, inc, Com.wvars])]
    exact hqpow
  have hord₁ : σ₁.arrs "ord" = arrOf n ord := by
    rw [r₁.frame_arr "ord" (by simp [clearArray, seqs, inc, Com.warrs])]
    exact hord
  have hkeys₁ : σ₁.arrs keyName = arrOf n key := by
    rw [r₁.frame_arr keyName (by
      simp [clearArray, seqs, inc, Com.warrs, hkeyCount])]
    exact hkeys
  have hscratch₁ : σ₁.arrs "scratchOrder" = arrOf n scratch := by
    rw [r₁.frame_arr "scratchOrder" (by
      simp [clearArray, seqs, inc, Com.warrs])]
    exact hscratch
  obtain ⟨σ₂, r₂, hcount₂, -⟩ :=
    countPhase_run halen₁ hqpow₁ hord₁ hordval hkeys₁ hcount₁ hzero₁
      hxn hnB hqB hvert hkey hkeyCount
  have halen₂ : σ₂.vars "alen" = xs.length := by
    rw [r₂.frame_var "alen" (by simp [seqs, inc, Com.wvars])]
    exact halen₁
  have hqpow₂ : σ₂.vars "qpow" = q := by
    rw [r₂.frame_var "qpow" (by simp [seqs, inc, Com.wvars])]
    exact hqpow₁
  have hord₂ : σ₂.arrs "ord" = arrOf n ord := by
    rw [r₂.frame_arr "ord" (by simp [seqs, inc, Com.warrs])]
    exact hord₁
  have hkeys₂ : σ₂.arrs keyName = arrOf n key := by
    rw [r₂.frame_arr keyName (by simp [seqs, inc, Com.warrs, hkeyCount])]
    exact hkeys₁
  have hscratch₂ : σ₂.arrs "scratchOrder" = arrOf n scratch := by
    rw [r₂.frame_arr "scratchOrder" (by simp [seqs, inc, Com.warrs])]
    exact hscratch₁
  obtain ⟨σ₃, r₃, hcount₃, -⟩ :=
    prefixPhase_run hqpow₂ hcount₂ (fun _ _ => rfl) hqB
      (lt_of_le_of_lt hxn hnB) hstart
  have halen₃ : σ₃.vars "alen" = xs.length := by
    rw [r₃.frame_var "alen" (by simp [seqs, inc, Com.wvars])]
    exact halen₂
  have hord₃ : σ₃.arrs "ord" = arrOf n ord := by
    rw [r₃.frame_arr "ord" (by simp [seqs, inc, Com.warrs])]
    exact hord₂
  have hkeys₃ : σ₃.arrs keyName = arrOf n key := by
    rw [r₃.frame_arr keyName (by simp [seqs, inc, Com.warrs, hkeyCount])]
    exact hkeys₂
  have hscratch₃ : σ₃.arrs "scratchOrder" = arrOf n scratch := by
    rw [r₃.frame_arr "scratchOrder" (by simp [seqs, inc, Com.warrs])]
    exact hscratch₂
  obtain ⟨σ₄, scratch₄, r₄, hscratch₄, hscratchval₄, -⟩ :=
    scatterPhase_run halen₃ hord₃ hordval hkeys₃ hcount₃
      (fun _ _ => rfl) hscratch₃ hkeyCount hkeyScratch hxn hnB hqB
      hxs hvert hkey hstart
  have halen₄ : σ₄.vars "alen" = xs.length := by
    rw [r₄.frame_var "alen" (by simp [seqs, inc, Com.wvars])]
    exact halen₃
  have hord₄ : σ₄.arrs "ord" = arrOf n ord := by
    rw [r₄.frame_arr "ord" (by simp [seqs, inc, Com.warrs])]
    exact hord₃
  let ys := bucketSort q key xs
  have hyslen : ys.length = xs.length := by
    exact (bucketSort_perm hxs hkey).length_eq
  have hysB : ∀ y ∈ ys, y < B := by
    intro y hy
    have hyx : y ∈ xs := (mem_bucketSort.mp hy).1
    exact (hvert y hyx).trans hnB
  obtain ⟨σ₅, ord₅, r₅, hord₅, hordval₅, -⟩ :=
    copyPhase_run (ys := ys) (by simpa [ys, hyslen] using halen₄)
      hscratch₄ (by
        intro i hi
        apply hscratchval₄ i
        rwa [hyslen] at hi) hord₄
      (by simpa [ys, hyslen] using hxn) hnB hysB
  have rr := r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))
  have hkeys₅ : σ₅.arrs keyName = arrOf n key := by
    rw [rr.frame_arr keyName (by
      simp [radixPass, clearArray, seqs, inc, Com.warrs,
        hkeyOrd, hkeyCount, hkeyScratch])]
    exact hkeys
  refine ⟨σ₅, ord₅, ?_, ?_, ?_, hord₅, ?_, hkeys₅⟩
  · have rb : Run B _ σ σ₅ (64 * (xs.length + q + 1)) :=
      rr.mono (by rw [hyslen]; omega)
    simpa [radixPass, seqs] using rb
  · rw [rr.frame_var "alen" (by
      simp [radixPass, clearArray, seqs, inc, Com.wvars])]
    exact halen
  · rw [rr.frame_var "qpow" (by
      simp [radixPass, clearArray, seqs, inc, Com.wvars])]
    exact hqpow
  · intro i hi
    apply hordval₅ i
    simpa [hyslen] using hi

end Lax235315Proofs.Construction.RadixPass
