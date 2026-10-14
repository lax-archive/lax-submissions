import Mathlib.Tactic
import Lax235315Proofs.Construction.RandomBits
import Lax235315Proofs.Construction.RandomKeyEquiv
import Lax457868Proofs.FairBitIndices

/-!
The IMP+ implementation of the finite fair-bit rejection selector. Each
attempt calls the existing binary key reader, so a block is consumed exactly
as one `readKeyDigit "key0"` operation.
-/

namespace Lax457868Proofs.FairBitRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.RandomBits
open Lax235315Proofs.Construction.RandomKeyEquiv
open Lax457868Proofs.FairBitIndices

/-- The finite source command that reads blocks until one is accepted or the
cap is reached. `drawStop` is shortened to the number already consumed when
an accepted block is found, so the loop halts at that exact attempt. -/
private def selectorBody : Com :=
  seqs [readKeyDigit "key0",
    .assign "drawValue" (.get "key0" (.var "v")),
    inc "drawUsed",
    .ite (.lt (.var "drawValue") (.var "drawModulus"))
      (seqs [.assign "drawFound" (.lit 1),
        .assign "drawStop" (.var "drawUsed")]) .skip]

/-- The capped rejection loop. Its initial stop is the cap; acceptance sets
the stop to the current draw count. -/
private def selectorLoop : Com :=
  .while (.lt (.var "drawUsed") (.var "drawStop")) selectorBody

/-- Initialize the counters and run the finite rejection loop. -/
def countedRejectionSelector : Com :=
  seqs [
    .assign "drawUsed" (.lit 0),
    .assign "drawFound" (.lit 0),
    .assign "drawValue" (.lit 0),
    .assign "drawStop" (.var "drawCap"),
    selectorLoop]

/-- Flatten a list of independent blocks in the order consumed by the reader.
-/
def flattenBitBlockList {L : ℕ} : List (Fin L → Bool) → List ℕ
  | [] => []
  | bits :: rest =>
      Lax195003.WordRamRandomness.bitTape bits ++ flattenBitBlockList rest

/-- The recursive flattening is list `flatMap` over the word-RAM bit tape. -/
lemma flattenBitBlockList_eq_flatMap {L : ℕ} (blocks : List (Fin L → Bool)) :
    flattenBitBlockList blocks = blocks.flatMap Lax195003.WordRamRandomness.bitTape := by
  induction blocks with
  | nil => rfl
  | cons bits blocks ih => simp [flattenBitBlockList, ih]

/-- The decoded result and actual capped attempt count for a block list. -/
def decodeBlockIndex (m : ℕ) {L : ℕ} (bits : Fin L → Bool) : Option (Fin m) :=
  if h : bitBlockValue bits < m then some ⟨bitBlockValue bits, h⟩ else none

/-- The decoded result and actual capped attempt count for a block list. -/
def listSelection {L : ℕ} (m : ℕ) (blocks : List (Fin L → Bool)) :=
  firstDecodedWithCount (blocks.map (decodeBlockIndex m))

private lemma runWhileTrue {B : ℕ} {b : Cond} {c : Com}
    {σ σ₁ σ₂ : Env} {P Q : ℕ}
    (hb : b.evalB B σ = some true)
    (hbody : Run B c σ σ₁ P)
    (hloop : Run B (.while b c) σ₁ σ₂ Q) :
    Run B (.while b c) σ σ₂ (1 + b.size + P + Q) := by
  obtain ⟨k, hk, hbs⟩ := hbody
  obtain ⟨k', hk', hbs'⟩ := hloop
  exact ⟨1 + b.size + k + k', by omega,
    BigStepB.while_true hb hbs hbs'⟩

/-- Flatten a tape of independent bit blocks into the source reader's input
format: each block's most-significant-bit-first words are consecutive. -/
def flattenBitBlocks {L t : ℕ}
    (tape : Fin t → (Fin L → Bool)) : List ℕ :=
  (List.ofFn tape).flatMap Lax195003.WordRamRandomness.bitTape

/-- Splitting off the first independent block exposes precisely the input
prefix consumed by `readKeyDigit "key0"`. -/
lemma flattenBitBlocks_succ {L t : ℕ}
    (tape : Fin (t + 1) → (Fin L → Bool)) :
    flattenBitBlocks tape =
      Lax195003.WordRamRandomness.bitTape (tape 0) ++
        flattenBitBlocks (fun i => tape i.succ) := by
  simp [flattenBitBlocks, List.ofFn_succ, List.flatMap_cons]

/-- The flattened input contains exactly `L` words per block. -/
lemma flattenBitBlocks_length {L t : ℕ}
    (tape : Fin t → (Fin L → Bool)) :
    (flattenBitBlocks tape).length = t * L := by
  induction t with
  | zero => simp [flattenBitBlocks]
  | succ t ih =>
      rw [flattenBitBlocks_succ]
      simp [List.length_append, Lax195003.WordRamRandomness.bitTape, ih]
      rw [Nat.succ_mul]
      omega

/-- The reader's most-significant-bit-first value agrees exactly with the
finite fair-bit block decoder. -/
lemma bitBlockValue_eq_bitsValue {L : ℕ} (bits : Fin L → Bool) :
    bitBlockValue bits = bitsValue (Lax195003.WordRamRandomness.bitTape bits) := by
  unfold bitBlockValue
  symm
  exact bitsValue_eq_ofDigits_reverse _

/-- Reading a single fair-bit block through the existing `key0` reader stores
the value decoded by `FairBitIndices.bitBlockValue`, consumes exactly the
block, and retains the reader's source cost bound. -/
lemma readBitBlock_run {B n v L : ℕ} {σ : Env} {g : ℕ → ℕ}
    {bits : Fin L → Bool} {rest : List ℕ}
    (hkey : σ.arrs "key0" = arrOf n g)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hL : σ.vars "L" = L)
    (hinp : σ.inp = Lax195003.WordRamRandomness.bitTape bits ++ rest)
    (hpowB : 2 ^ L < B) (hnB : n < B) (htwoB : 2 < B) :
    ∃ σ' g', Run B (readKeyDigit "key0") σ σ' (15 * L + 11) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      g' v = bitBlockValue bits ∧
      (∀ i < n, i ≠ v → g' i = g i) ∧ σ'.inp = rest ∧
      σ'.vars "v" = v ∧ σ'.vars "L" = L := by
  have hbs : (Lax195003.WordRamRandomness.bitTape bits).length = L := by
    simp [Lax195003.WordRamRandomness.bitTape]
  have hbits : ∀ b ∈ Lax195003.WordRamRandomness.bitTape bits, b ≤ 1 := by
    intro b hb
    simp only [Lax195003.WordRamRandomness.bitTape, List.mem_ofFn] at hb
    rcases hb with ⟨i, rfl⟩
    cases bits i <;> decide
  obtain ⟨σ', g', hr, harr, hval, hframe, hinp', hv', hL'⟩ :=
    Lax235315Proofs.Construction.RandomBits.readKeyDigit_run
      hkey hv hvn hL hbs hinp hbits hpowB hnB htwoB
  refine ⟨σ', g', hr, harr, ?_, hframe, hinp', hv', hL'⟩
  rw [bitBlockValue_eq_bitsValue]
  exact hval

/-- One loop iteration runs the existing reader and advances the counted
selector by one block. The branch is determined by the block's decoded value.
-/
lemma selectorBody_run {B n v L m used stop : ℕ} {σ : Env} {g : ℕ → ℕ}
    {bits : Fin L → Bool} {rest : List ℕ}
    (hkey : σ.arrs "key0" = arrOf n g)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hL : σ.vars "L" = L)
    (hused : σ.vars "drawUsed" = used)
    (hfound : σ.vars "drawFound" = 0)
    (hstop : σ.vars "drawStop" = stop)
    (hmod : σ.vars "drawModulus" = m)
    (hinp : σ.inp = Lax195003.WordRamRandomness.bitTape bits ++ rest)
    (hpowB : 2 ^ L < B) (hnB : n < B) (htwoB : 2 < B)
    (hmodB : m < B)
    (hnextB : used + 1 < B) :
    ∃ σ' g', Run B selectorBody σ σ'
        (if bitBlockValue bits < m then 15 * L + 26 else 15 * L + 23) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      g' v = bitBlockValue bits ∧
      (∀ i < n, i ≠ v → g' i = g i) ∧ σ'.inp = rest ∧
      σ'.vars "v" = v ∧ σ'.vars "L" = L ∧
      σ'.vars "drawUsed" = used + 1 ∧
      σ'.vars "drawValue" = bitBlockValue bits ∧
      σ'.vars "drawFound" = (if bitBlockValue bits < m then 1 else 0) ∧
      σ'.vars "drawStop" = (if bitBlockValue bits < m then used + 1 else stop) := by
  obtain ⟨σr, gr, hread, harray, hvalue, hframe, hinpr, hvr, hLr⟩ :=
    readBitBlock_run hkey hv hvn hL hinp hpowB hnB htwoB
  let d := bitBlockValue bits
  have hdB : d < B := lt_of_lt_of_le (bitBlockValue_lt bits) hpowB.le
  have hvrvar : σr.vars "v" < B := by simpa [hvr] using hvn.trans hnB
  have hget : (Expr.get "key0" (.var "v")).evalB B σr = some d := by
    apply evalB_get (evalB_var hvrvar) _ hdB
    rw [hvr, harray, getElem?_arrOf _ hvn]
    exact congrArg some hvalue
  let σ₁ := σr.setVar "drawValue" d
  have hassign : Run B (.assign "drawValue" (.get "key0" (.var "v")))
      σr σ₁ 3 := by
    simpa [σ₁] using (Run.assign hget)
  have hdrawB : σ₁.vars "drawValue" = d := by simp [σ₁]
  have husedr : σr.vars "drawUsed" = used := by
    rw [hread.frame_var "drawUsed" (by decide), hused]
  have hfoundr : σr.vars "drawFound" = 0 := by
    rw [hread.frame_var "drawFound" (by decide), hfound]
  have hstopr : σr.vars "drawStop" = stop := by
    rw [hread.frame_var "drawStop" (by decide), hstop]
  have hmodr : σr.vars "drawModulus" = m := by
    rw [hread.frame_var "drawModulus" (by decide), hmod]
  let σ₂ := σ₁.setVar "drawUsed" (used + 1)
  have hadd : (Expr.add (.var "drawUsed") (.lit 1)).evalB B σ₁ = some (used + 1) := by
    change (Expr.bin Bop.add (.var "drawUsed") (.lit 1)).evalB B σ₁ = some (used + 1)
    have husedB : σ₁.vars "drawUsed" < B := by
      simp [σ₁, husedr]
      omega
    have haddB : Bop.apply Bop.add (σ₁.vars "drawUsed") 1 < B := by
      simp [Bop.apply, σ₁, husedr]
      omega
    have hbin := evalB_bin (evalB_var husedB) (evalB_lit (by omega : 1 < B)) haddB
    simpa [Bop.apply, σ₁, husedr] using hbin
  have hinc : Run B (inc "drawUsed") σ₁ σ₂ 4 := by
    simpa [inc, σ₂] using (Run.assign hadd)
  have hbcond : (Cond.lt (.var "drawValue") (.var "drawModulus")).evalB B σ₂ =
      some (decide (d < m)) := by
    have hdraw2B : σ₂.vars "drawValue" < B := by
      simpa [σ₂, σ₁, hdrawB] using hdB
    have hmod2 : σ₂.vars "drawModulus" < B := by
      simpa [σ₂, σ₁, hmodr] using hmodB
    apply evalB_condLt
    · simpa [σ₂, σ₁, hdrawB] using (evalB_var hdraw2B)
    · simpa [σ₂, σ₁, hmodr] using (evalB_var hmod2)
  have hfound0 : σ₂.vars "drawFound" = 0 := by simp [σ₂, σ₁, hfoundr]
  have hstop2 : σ₂.vars "drawStop" = stop := by simp [σ₂, σ₁, hstopr]
  by_cases hd : d < m
  · let σ₃ := σ₂.setVar "drawFound" 1
    have hfoundAssign : Run B (.assign "drawFound" (.lit 1)) σ₂ σ₃ 2 := by
      simpa [σ₃] using (Run.assign (evalB_lit (by omega : 1 < B)))
    have hused3B : σ₃.vars "drawUsed" < B := by
      simp [σ₃, σ₂, σ₁, husedr]
      exact hnextB
    have hstopvar : (Expr.var "drawUsed").evalB B σ₃ = some (used + 1) := by
      simpa [σ₃, σ₂, σ₁, husedr] using (evalB_var hused3B)
    let σ₄ := σ₃.setVar "drawStop" (used + 1)
    have hstopAssign : Run B (.assign "drawStop" (.var "drawUsed")) σ₃ σ₄ 2 := by
      simpa [σ₄] using (Run.assign hstopvar)
    have hacceptBranch : Run B
        (seqs [.assign "drawFound" (.lit 1), .assign "drawStop" (.var "drawUsed")])
        σ₂ σ₄ 4 := by
      simpa [seqs] using (Run.seq hfoundAssign hstopAssign)
    have hite : Run B
        (.ite (.lt (.var "drawValue") (.var "drawModulus"))
          (seqs [.assign "drawFound" (.lit 1), .assign "drawStop" (.var "drawUsed")]) .skip)
        σ₂ σ₄ 8 := by
      exact Run.ite_true (by simpa [hd] using hbcond) hacceptBranch
    refine ⟨σ₄, gr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change Run B selectorBody σ σ₄ (if d < m then 15 * L + 26 else 15 * L + 23)
      have hseq := Run.seq hread (Run.seq hassign (Run.seq hinc hite))
      simpa [selectorBody, seqs, Nat.add_assoc, d, hd] using hseq
    · simp [σ₄, σ₃, σ₂, σ₁, harray]
    · exact hvalue
    · intro i hi hiv
      exact hframe i hi hiv
    · simpa [σ₄, σ₃, σ₂, σ₁] using hinpr
    · simpa [σ₄, σ₃, σ₂, σ₁] using hvr
    · simpa [σ₄, σ₃, σ₂, σ₁] using hLr
    · simp [σ₄, σ₃, σ₂, σ₁]
    · simp [σ₄, σ₃, σ₂, σ₁, d]
    · simp [σ₄, σ₃, σ₂, σ₁, d, hd]
    · simp [σ₄, σ₃, σ₂, σ₁, d, hd]
  · let σ₃ := σ₂
    have hrejected : Run B
        (.ite (.lt (.var "drawValue") (.var "drawModulus"))
          (seqs [.assign "drawFound" (.lit 1), .assign "drawStop" (.var "drawUsed")]) .skip)
        σ₂ σ₃ 5 := by
      exact Run.ite_false (by simpa [hd] using hbcond) Run.skip
    refine ⟨σ₃, gr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change Run B selectorBody σ σ₃ (if d < m then 15 * L + 26 else 15 * L + 23)
      have hseq := Run.seq hread (Run.seq hassign (Run.seq hinc hrejected))
      simpa [selectorBody, seqs, Nat.add_assoc, d, hd] using hseq
    · simp [σ₃, σ₂, σ₁, harray]
    · exact hvalue
    · intro i hi hiv
      exact hframe i hi hiv
    · simpa [σ₃, σ₂, σ₁] using hinpr
    · simpa [σ₃, σ₂, σ₁] using hvr
    · simpa [σ₃, σ₂, σ₁] using hLr
    · simp [σ₃, σ₂, σ₁]
    · simp [σ₃, σ₂, σ₁, d]
    · simp [σ₃, σ₂, σ₁, hfound0, hfoundr, d, hd]
    · simp [σ₃, σ₂, σ₁, hstop2, hstopr, d, hd]

/-- The counted source loop consumes the initial blocks through and including
the first accepted block, or all blocks if the list is exhausted. The source
cost is affine in that exact consumed count. -/
lemma selectorLoop_run_list {B n v L m cap used : ℕ}
    {σ : Env} {g : ℕ → ℕ} {blocks : List (Fin L → Bool)} {rest : List ℕ}
    (hm : 0 < m)
    (hlen : blocks.length = cap - used)
    (husedCap : used ≤ cap)
    (hkey : σ.arrs "key0" = arrOf n g)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hL : σ.vars "L" = L)
    (hused : σ.vars "drawUsed" = used)
    (hfound : σ.vars "drawFound" = 0)
    (hstop : σ.vars "drawStop" = cap)
    (hmod : σ.vars "drawModulus" = m)
    (hinp : σ.inp = flattenBitBlockList blocks ++ rest)
    (hpowB : 2 ^ L < B) (hnB : n < B) (htwoB : 2 < B)
    (hcapB : cap < B) (hmodB : m < B) :
    ∃ σ' g', Run B selectorLoop σ σ'
        ((15 * L + 30) * (listSelection m blocks).2 + 4) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      (∀ i < n, i ≠ v → g' i = g i) ∧
      σ'.inp = flattenBitBlockList
        (blocks.drop (listSelection m blocks).2) ++ rest ∧
      σ'.vars "v" = v ∧ σ'.vars "L" = L ∧
      σ'.vars "drawUsed" = used + (listSelection m blocks).2 ∧
      (∀ i, (listSelection m blocks).1 = some i → σ'.vars "drawValue" = i.val) ∧
      (∀ i, (listSelection m blocks).1 = some i → g' v = i.val) ∧
      σ'.vars "drawFound" = (if (listSelection m blocks).1 = none then 0 else 1) ∧
      σ'.vars "drawStop" = (if (listSelection m blocks).1 = none
        then cap else used + (listSelection m blocks).2) := by
  induction blocks generalizing σ g used husedCap with
  | nil =>
      have hsub : cap - used = 0 := by simpa using hlen.symm
      have huc : used = cap := by omega
      have hguard : (Cond.lt (.var "drawUsed") (.var "drawStop")).evalB B σ = some false := by
        have husedB : σ.vars "drawUsed" < B := by rw [hused, huc]; exact hcapB
        have hstopB : σ.vars "drawStop" < B := by rw [hstop]; exact hcapB
        have h := evalB_condLt (evalB_var husedB) (evalB_var hstopB)
        simpa [hused, hstop, huc] using h
      refine ⟨σ, g, ?_, hkey, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [selectorLoop, listSelection, firstDecodedWithCount] using Run.while_false hguard
      · intro i hi hiv; rfl
      · simpa [flattenBitBlockList]
      · exact hv
      · exact hL
      · simp [listSelection, firstDecodedWithCount, hused, huc]
      · intro i hi
        simp [listSelection, firstDecodedWithCount] at hi
      · intro i hi
        simp [listSelection, firstDecodedWithCount] at hi
      · simp [listSelection, firstDecodedWithCount, hfound, hstop]
  | cons bits blocks ih =>
      have hlen' : blocks.length = cap - (used + 1) := by
        simp only [List.length_cons] at hlen
        omega
      have husedlt : used < cap := by
        simp only [List.length_cons] at hlen
        omega
      have hnextB : used + 1 < B := by omega
      have htrue : (Cond.lt (.var "drawUsed") (.var "drawStop")).evalB B σ = some true := by
        have husedB : σ.vars "drawUsed" < B := by rw [hused]; omega
        have hstopB : σ.vars "drawStop" < B := by rw [hstop]; exact hcapB
        have h := evalB_condLt (evalB_var husedB) (evalB_var hstopB)
        simpa [hused, hstop, husedlt] using h
      have hinput : σ.inp =
          Lax195003.WordRamRandomness.bitTape bits ++ (flattenBitBlockList blocks ++ rest) := by
        simpa [flattenBitBlockList, List.append_assoc] using hinp
      obtain ⟨σ₁, g₁, hbody, harray, hvalue, hframe, hinp₁,
          hv₁, hL₁, hused₁, hdraw₁, hfound₁, hstop₁⟩ :=
        selectorBody_run hkey hv hvn hL hused hfound hstop hmod
          hinput hpowB hnB htwoB hmodB hnextB
      by_cases haccept : bitBlockValue bits < m
      · have hfoundTrue : σ₁.vars "drawFound" = 1 := by simpa [haccept] using hfound₁
        have hstopTrue : σ₁.vars "drawStop" = used + 1 := by simpa [haccept] using hstop₁
        have hfalse : (Cond.lt (.var "drawUsed") (.var "drawStop")).evalB B σ₁ = some false := by
          have hused1B : σ₁.vars "drawUsed" < B := by rw [hused₁]; exact hnextB
          have hstop1B : σ₁.vars "drawStop" < B := by rw [hstopTrue]; exact hnextB
          have h := evalB_condLt (evalB_var hused1B) (evalB_var hstop1B)
          simpa [hused₁, hstopTrue] using h
        have hhalt := Run.while_false (c := selectorBody) hfalse
        have hloop := runWhileTrue htrue hbody hhalt
        have htest : 1 + (Cond.lt (.var "drawUsed") (.var "drawStop")).size = 4 := by decide
        have hpure : listSelection m (bits :: blocks) =
            (some ⟨bitBlockValue bits, by omega⟩, 1) := by
          simp [listSelection, decodeBlockIndex, firstDecodedWithCount, haccept]
        refine ⟨σ₁, g₁, ?_, harray, hframe, ?_, hv₁, hL₁, ?_, ?_, ?_, ?_, ?_⟩
        · have hcmp :
              ((1 + (Cond.lt (.var "drawUsed") (.var "drawStop")).size +
                  (if bitBlockValue bits < m then 15 * L + 26 else 15 * L + 23)) +
                (1 + (Cond.lt (.var "drawUsed") (.var "drawStop")).size)) ≤
                15 * L + 34 := by
            rw [htest]
            simp [haccept]
            omega
          have hcost := hloop.mono hcmp
          simpa [selectorLoop, hpure, firstDecodedWithCount, Nat.add_assoc] using hcost
        · simpa [hpure, flattenBitBlockList]
            using (show σ₁.inp = flattenBitBlockList blocks ++ rest from hinp₁)
        · simp [hpure, hused₁]
        · intro i hi
          simp [hpure] at hi
          cases hi
          simpa using hdraw₁
        · intro i hi
          simp [hpure] at hi
          cases hi
          exact hvalue
        · simp [hpure, hfoundTrue]
        · simp [hpure, hstopTrue]
      · have hfoundFalse : σ₁.vars "drawFound" = 0 := by simpa [haccept] using hfound₁
        have hstopFalse : σ₁.vars "drawStop" = cap := by simpa [haccept] using hstop₁
        have hmod₁ : σ₁.vars "drawModulus" = m := by
          rw [hbody.frame_var "drawModulus" (by decide), hmod]
        have hkey₁ : σ₁.arrs "key0" = arrOf n g₁ := harray
        have hrecinp : σ₁.inp = flattenBitBlockList blocks ++ rest := hinp₁
        obtain ⟨σ₂, g₂, hrec, harray₂, hframe₂, hinp₂, hv₂, hL₂,
            hused₂, hdraw₂, hkeyValue₂, hfound₂, hstop₂⟩ :=
          ih hlen' (by omega) hkey₁ hv₁ hL₁ hused₁ hfoundFalse hstopFalse hmod₁
            hrecinp
        have hloop := runWhileTrue htrue hbody hrec
        have htest : 1 + (Cond.lt (.var "drawUsed") (.var "drawStop")).size = 4 := by decide
        have hpure : listSelection m (bits :: blocks) =
            ((listSelection m blocks).1,
              (listSelection m blocks).2 + 1) := by
          simp [listSelection, decodeBlockIndex, firstDecodedWithCount, haccept]
        have hframeFinal : ∀ i < n, i ≠ v → g₂ i = g i := by
          intro i hi hiv
          rw [hframe₂ i hi hiv, hframe i hi hiv]
        refine ⟨σ₂, g₂, ?_, harray₂, hframeFinal, ?_, hv₂, hL₂, ?_, ?_, ?_, ?_, ?_⟩
        · have hcmp :
              ((1 + (Cond.lt (.var "drawUsed") (.var "drawStop")).size +
                  (if bitBlockValue bits < m then 15 * L + 26 else 15 * L + 23)) +
                ((15 * L + 30) * (listSelection m blocks).2 + 4)) ≤
                (15 * L + 30) * ((listSelection m blocks).2 + 1) + 4 := by
            rw [htest]
            simp [haccept]
            have hfactor : (15 * L + 30) * ((listSelection m blocks).2 + 1) =
                (15 * L + 30) * (listSelection m blocks).2 + (15 * L + 30) := by ring
            rw [hfactor]
            omega
          have hcost := hloop.mono hcmp
          simpa [selectorLoop, hpure, firstDecodedWithCount, Nat.add_assoc] using hcost
        · have hdrop : List.drop (listSelection m (bits :: blocks)).2 (bits :: blocks) =
              List.drop (listSelection m blocks).2 blocks := by
            rw [hpure]
            simp [List.drop_succ_cons]
          rw [hdrop]
          exact hinp₂
        · simp only [hpure, Prod.snd] at hused₂ ⊢
          omega
        · intro i hi
          have htail : (listSelection m blocks).1 = some i := by simpa [hpure] using hi
          exact hdraw₂ i htail
        · intro i hi
          have htail : (listSelection m blocks).1 = some i := by simpa [hpure] using hi
          exact hkeyValue₂ i htail
        · simpa [hpure] using hfound₂
        · by_cases hnone : (listSelection m blocks).1 = none
          · simpa [hpure, hnone] using hstop₂
          · simp [hpure, hnone] at hstop₂ ⊢
            rw [Nat.add_assoc] at hstop₂
            rw [Nat.add_comm 1 (listSelection m blocks).2] at hstop₂
            exact hstop₂


/-- The generic list scan is the concrete fair-bit tape selector. -/
lemma listSelection_ofFn (m : ℕ) (hm : 0 < m) (t : ℕ)
    (tape : BitTape m t) :
    listSelection m (List.ofFn tape) = selectBitIndexWithCount m hm t tape := by
  change firstDecodedWithCount ((List.ofFn tape).map (decodeBlockIndex m)) =
    firstDecodedWithCount ((List.ofFn tape).map (decodeBitIndex m hm))
  rfl

/-- Run the source-level counted rejection selector on a flattened finite tape.
It consumes exactly the attempted blocks, preserves every key cell other than
`v`, and stores the selected index in both the current key cell and
`drawValue` when an accepted block exists. The source execution cost is bounded
affinely in the actual attempt count and block width. -/
lemma countedRejectionSelector_run_tape {B n v m t : ℕ}
    {σ : Env} {g : ℕ → ℕ} {rest : List ℕ}
    (tape : BitTape m t) (hm : 0 < m)
    (hkey : σ.arrs "key0" = arrOf n g)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hL : σ.vars "L" = Nat.clog 2 m)
    (hmod : σ.vars "drawModulus" = m)
    (hcap : σ.vars "drawCap" = t)
    (hinp : σ.inp = flattenBitBlocks tape ++ rest)
    (hpowB : 2 ^ Nat.clog 2 m < B) (hnB : n < B) (htwoB : 2 < B)
    (htB : t < B) (hmB : m < B) :
    ∃ σ' g',
      Run B countedRejectionSelector σ σ'
        ((15 * Nat.clog 2 m + 30) * bitTapeAttemptsUsed m t
          tape + 12) ∧
      σ'.arrs "key0" = arrOf n g' ∧
      (∀ i < n, i ≠ v → g' i = g i) ∧
      (∀ i, (selectBitIndexWithCount m hm t
          tape).1 = some i →
        g' v = i.val ∧ σ'.vars "drawValue" = i.val) ∧
      σ'.vars "drawUsed" = bitTapeAttemptsUsed m t
        tape ∧
      σ'.vars "drawFound" = (if (selectBitIndexWithCount m hm t
        tape).1 = none then 0 else 1) ∧
      σ'.inp = flattenBitBlockList
        ((List.ofFn tape).drop
          (bitTapeAttemptsUsed m t tape)) ++ rest ∧
      σ'.vars "v" = v ∧ σ'.vars "L" = Nat.clog 2 m ∧
      σ'.vars "drawModulus" = m ∧ σ'.vars "drawCap" = t ∧
      (∀ a, a ≠ "key0" → σ'.arrs a = σ.arrs a) := by
  let blocks := List.ofFn tape
  let σ₀ := σ.setVar "drawUsed" 0
  let σ₁ := σ₀.setVar "drawFound" 0
  let σ₂ := σ₁.setVar "drawValue" 0
  let σ₃ := σ₂.setVar "drawStop" t
  have h0 : Run B (.assign "drawUsed" (.lit 0)) σ σ₀ 2 := by
    simpa [σ₀] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have h1 : Run B (.assign "drawFound" (.lit 0)) σ₀ σ₁ 2 := by
    simpa [σ₁] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have h2 : Run B (.assign "drawValue" (.lit 0)) σ₁ σ₂ 2 := by
    simpa [σ₂] using (Run.assign (evalB_lit (by omega : 0 < B)))
  have hcap2 : σ₂.vars "drawCap" = t := by simp [σ₂, σ₁, σ₀, hcap]
  have hcapB : σ₂.vars "drawCap" < B := by rw [hcap2]; exact htB
  have hstopEval : (Expr.var "drawCap").evalB B σ₂ = some t := by
    simpa [hcap2] using (evalB_var hcapB)
  have h3 : Run B (.assign "drawStop" (.var "drawCap")) σ₂ σ₃ 2 := by
    simpa [σ₃] using (Run.assign hstopEval)
  have hinit : Run B (seqs [
      .assign "drawUsed" (.lit 0), .assign "drawFound" (.lit 0),
      .assign "drawValue" (.lit 0), .assign "drawStop" (.var "drawCap")])
      σ σ₃ 8 := by
    simpa [seqs, σ₀, σ₁, σ₂, σ₃, Nat.add_assoc] using Run.seq h0 (Run.seq h1 (Run.seq h2 h3))
  have hkey₃ : σ₃.arrs "key0" = arrOf n g := by simp [σ₃, σ₂, σ₁, σ₀, hkey]
  have hv₃ : σ₃.vars "v" = v := by simp [σ₃, σ₂, σ₁, σ₀, hv]
  have hL₃ : σ₃.vars "L" = Nat.clog 2 m := by simp [σ₃, σ₂, σ₁, σ₀, hL]
  have hmod₃ : σ₃.vars "drawModulus" = m := by simp [σ₃, σ₂, σ₁, σ₀, hmod]
  have hflat : flattenBitBlocks tape = flattenBitBlockList blocks := by
    simp [flattenBitBlocks, blocks, flattenBitBlockList_eq_flatMap]
  have hinput₃ : σ₃.inp = flattenBitBlockList blocks ++ rest := by
    simpa [σ₃, σ₂, σ₁, σ₀, hflat] using hinp
  have hblocks : blocks.length = t := by simp [blocks]
  obtain ⟨σ₄, g', hloop, harray, hframe, hinp₄, hv₄, hL₄,
      hused₄, hdraw₄, hkeyval₄, hfound₄, hstop₄⟩ :=
    selectorLoop_run_list (B := B) (n := n) (v := v) (L := Nat.clog 2 m)
      (m := m) (cap := t) (used := 0) (σ := σ₃) (g := g)
      (blocks := blocks) (rest := rest) hm
      (by simpa [blocks] using hblocks) (by omega)
      hkey₃ hv₃ hvn hL₃ (by simp [σ₃, σ₂, σ₁, σ₀])
      (by simp [σ₃, σ₂, σ₁, σ₀])
      (by simp [σ₃, σ₂, σ₁, σ₀]) hmod₃ hinput₃
      hpowB hnB htwoB htB hmB
  let pureCount := selectBitIndexWithCount m hm t tape
  have hpure : listSelection m blocks = pureCount := by
    exact listSelection_ofFn m hm t tape
  have hwhole : Run B countedRejectionSelector σ σ₄
      ((15 * Nat.clog 2 m + 30) * pureCount.2 + 12) := by
    have hseq := Run.seq h0 (Run.seq h1 (Run.seq h2 (Run.seq h3 hloop)))
    have hcmp :
        2 + (2 + (2 + (2 + ((15 * Nat.clog 2 m + 30) * pureCount.2 + 4)))) ≤
          (15 * Nat.clog 2 m + 30) * pureCount.2 + 12 := by omega
    have hseq' := hseq.mono hcmp
    simpa [countedRejectionSelector, selectorLoop, seqs, σ₀, σ₁, σ₂, σ₃,
      hpure] using hseq'
  refine ⟨σ₄, g', ?_, harray, hframe, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pureCount, bitTapeAttemptsUsed, selectBitIndexWithCount_eq m hm t tape]
      using hwhole
  · intro i hi
    have hsel : (listSelection m blocks).1 = some i := by
      simpa [pureCount, hpure] using hi
    exact ⟨hkeyval₄ i hsel, hdraw₄ i hsel⟩
  · simpa [pureCount, hpure, hused₄, Nat.zero_add,
      selectBitIndexWithCount_eq m hm t tape]
  · simpa [pureCount, hpure, hfound₄, selectBitIndexWithCount_eq m hm t tape]
  · simpa [pureCount, hpure, hinp₄, blocks, selectBitIndexWithCount_eq m hm t tape]
  · exact hv₄
  · exact hL₄
  · simpa [hmod] using hwhole.frame_var "drawModulus" (by decide)
  · constructor
    · simpa [hcap] using hwhole.frame_var "drawCap" (by decide)
    · have hWritten : countedRejectionSelector.warrs = ["key0"] := by
        simp [countedRejectionSelector, selectorLoop, selectorBody, seqs,
          readKeyDigit, inc, Com.warrs]
      intro a ha
      exact hwhole.frame_arr a (by simpa [hWritten] using ha)


end Lax457868Proofs.FairBitRam
