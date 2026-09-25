import Lax235315Proofs.Construction.RandomKeysRead
import Lax808846Proofs.Lib.Fill
import Mathlib.Tactic

/-! The active-set scan which reads one eight-digit random key per vertex. -/

namespace Lax235315Proofs.Construction.ReadKeys

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.RandomBits
open Lax235315Proofs.Construction.RandomKeysRead
open Lax235315Proofs.Construction.WelzlProgram

private theorem keyName_ne_ord (d : Fin 8) : keyName d ≠ "ord" := by
  fin_cases d <;> decide

/-- Increasing active vertices in the half-open integer interval
`[start, start + count)`. -/
def scanList (active : ℕ → ℕ) (start : ℕ) : ℕ → List ℕ
  | 0 => []
  | count + 1 =>
      if active start = 1 then
        start :: scanList active (start + 1) count
      else scanList active (start + 1) count

theorem scanList_add (active : ℕ → ℕ) (start first second : ℕ) :
    scanList active start (first + second) =
      scanList active start first ++ scanList active (start + first) second := by
  induction first generalizing start with
  | zero => simp [scanList]
  | succ first ih =>
      simp only [Nat.succ_add, scanList]
      rw [ih (start + 1)]
      have hstart : start + 1 + first = start + (first + 1) := by omega
      rw [hstart]
      split <;> rfl

theorem scanList_zero_add (active : ℕ → ℕ) (v : ℕ) :
    scanList active 0 (v + 1) =
      scanList active 0 v ++
        if active v = 1 then [v] else [] := by
  rw [show v + 1 = v + 1 by rfl, scanList_add]
  simp [scanList]

theorem scanList_remaining {active : ℕ → ℕ} {v n : ℕ} (hv : v < n) :
    scanList active v (n - v) =
      if active v = 1 then
        v :: scanList active (v + 1) (n - (v + 1))
      else scanList active (v + 1) (n - (v + 1)) := by
  conv_lhs => rw [show n - v = (n - (v + 1)) + 1 by omega]
  simp [scanList]

theorem scanList_length_le (active : ℕ → ℕ) (start count : ℕ) :
    (scanList active start count).length ≤ count := by
  induction count generalizing start with
  | zero => simp [scanList]
  | succ count ih =>
      simp only [scanList]
      split
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (ih (start + 1))
      · exact (ih (start + 1)).trans (Nat.le_succ count)

theorem mem_scanList {active : ℕ → ℕ} {start count v : ℕ} :
    v ∈ scanList active start count ↔
      start ≤ v ∧ v < start + count ∧ active v = 1 := by
  induction count generalizing start with
  | zero =>
      constructor
      · simp [scanList]
      · rintro ⟨hlo, hhi, -⟩
        omega
  | succ count ih =>
      by_cases hs : active start = 1
      · simp only [scanList, if_pos hs, List.mem_cons, ih]
        constructor
        · intro h
          rcases h with rfl | ⟨hlo, hhi, ha⟩
          · exact ⟨Nat.le_refl _, by omega, hs⟩
          · exact ⟨by omega, by omega, ha⟩
        · rintro ⟨hlo, hhi, ha⟩
          by_cases hv : v = start
          · exact Or.inl hv
          · exact Or.inr ⟨by omega, by omega, ha⟩
      · simp only [scanList, if_neg hs, ih]
        constructor
        · rintro ⟨hlo, hhi, ha⟩
          exact ⟨by omega, by omega, ha⟩
        · rintro ⟨hlo, hhi, ha⟩
          have hv : v ≠ start := by
            intro hv
            subst v
            exact hs ha
          exact ⟨by omega, by omega, ha⟩

theorem scanList_nodup (active : ℕ → ℕ) (start count : ℕ) :
    (scanList active start count).Nodup := by
  induction count generalizing start with
  | zero => simp [scanList]
  | succ count ih =>
      by_cases hs : active start = 1
      · simp only [scanList, if_pos hs, List.nodup_cons]
        refine ⟨?_, ih (start + 1)⟩
        rw [mem_scanList]
        omega
      · simpa [scanList, hs] using ih (start + 1)

theorem scanList_mem_range {active : ℕ → ℕ} {start count v : ℕ}
    (hv : v ∈ scanList active start count) : v < start + count :=
  (mem_scanList.mp hv).2.1

theorem scanList_active_getD {active : ℕ → ℕ} {v n : ℕ}
    (hv : v < n) (hav : active v = 1) :
    (scanList active 0 n).getD (scanList active 0 v).length 0 = v := by
  have hn : n = v + (n - v) := by omega
  rw [hn, scanList_add]
  simp only [Nat.zero_add]
  rw [scanList_remaining hv, if_pos hav]
  simp [List.getD_eq_getElem?_getD]

/-- The eight binary blocks consumed for a list of vertices. -/
def keyTape (bits : ℕ → Fin 8 → List ℕ) (vertices : List ℕ) : List ℕ :=
  vertices.flatMap fun v => joined8 (bits v)

@[simp] theorem keyTape_nil (bits : ℕ → Fin 8 → List ℕ) :
    keyTape bits [] = [] := rfl

@[simp] theorem keyTape_cons (bits : ℕ → Fin 8 → List ℕ) (v : ℕ)
    (vertices : List ℕ) :
    keyTape bits (v :: vertices) = joined8 (bits v) ++ keyTape bits vertices := rfl

theorem keyTape_append (bits : ℕ → Fin 8 → List ℕ) (xs ys : List ℕ) :
    keyTape bits (xs ++ ys) = keyTape bits xs ++ keyTape bits ys := by
  simp [keyTape]

/-- Key contents after precisely the vertices below `processed` have been
visited. -/
def filledKey (original : Fin 8 → ℕ → ℕ) (active : ℕ → ℕ)
    (bits : ℕ → Fin 8 → List ℕ) (processed : ℕ) (d : Fin 8) (i : ℕ) : ℕ :=
  if i < processed ∧ active i = 1 then bitsValue (bits i d) else original d i

@[simp] theorem filledKey_zero (original : Fin 8 → ℕ → ℕ) (active : ℕ → ℕ)
    (bits : ℕ → Fin 8 → List ℕ) (d : Fin 8) (i : ℕ) :
    filledKey original active bits 0 d i = original d i := by
  simp [filledKey]

theorem updateKeys_filledKey_succ {original : Fin 8 → ℕ → ℕ}
    {active : ℕ → ℕ} {bits : ℕ → Fin 8 → List ℕ} {v : ℕ}
    (hav : active v = 1) (d : Fin 8) :
    updateKeys (fun e => filledKey original active bits v e) (bits v) v d =
      filledKey original active bits (v + 1) d := by
  funext i
  unfold updateKeys filledKey
  by_cases hiv : i = v
  · subst i
    simp [hav]
  · have hiff : i < v + 1 ↔ i < v := by omega
    simp [hiv, hiff]

theorem filledKey_succ_of_inactive {original : Fin 8 → ℕ → ℕ}
    {active : ℕ → ℕ} {bits : ℕ → Fin 8 → List ℕ} {v : ℕ}
    (hav : active v ≠ 1) (d : Fin 8) :
    filledKey original active bits (v + 1) d =
      filledKey original active bits v d := by
  funext i
  unfold filledKey
  by_cases hiv : i = v
  · subst i
    simp [hav]
  · have hiff : i < v + 1 ↔ i < v := by omega
    simp [hiff]

/-- Loop invariant for `readKeys`. -/
def ReadKeysInv (n L : ℕ) (active : ℕ → ℕ)
    (original : Fin 8 → ℕ → ℕ) (bits : ℕ → Fin 8 → List ℕ)
    (rest : List ℕ) (τ : Env) : Prop :=
  τ.vars "v" ≤ n ∧ τ.vars "n" = n ∧ τ.vars "L" = L ∧
    τ.vars "alen" = (scanList active 0 (τ.vars "v")).length ∧
    τ.arrs "activeA" = arrOf n active ∧
    Fill.Below "ord" "alen" n
      (fun i => (scanList active 0 n).getD i 0) τ ∧
    (∀ d, τ.arrs (keyName d) =
      arrOf n (filledKey original active bits (τ.vars "v") d)) ∧
    τ.inp = keyTape bits (scanList active (τ.vars "v")
      (n - τ.vars "v")) ++ rest

private theorem joined8_lengths {L : ℕ} {b : Fin 8 → List ℕ}
    (hlen : ∀ d, (b d).length = L) : (joined8 b).length = 8 * L := by
  simp [joined8, hlen]
  omega

private theorem readKeys_body_spec {B n L : ℕ} {active : ℕ → ℕ}
    {original : Fin 8 → ℕ → ℕ} {bits : ℕ → Fin 8 → List ℕ}
    {rest : List ℕ}
    (hlen : ∀ v < n, ∀ d, (bits v d).length = L)
    (hbits : ∀ v < n, ∀ d x, x ∈ bits v d → x ≤ 1)
    (hactiveB : ∀ v < n, active v < B)
    (hpowB : 2 ^ L < B) (hnB : n < B) (htwoB : 2 < B) :
    Spec B
      (fun τ => ReadKeysInv n L active original bits rest τ ∧
        τ.vars "v" < n)
      (seqs [
        .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
          (seqs [.store "ord" (.var "alen") (.var "v"),
            readAllKeyDigits, inc "alen"])
          .skip,
        inc "v"])
      (fun τ τ' => ReadKeysInv n L active original bits rest τ' ∧
        τ'.vars "v" = τ.vars "v" + 1)
      (120 * L + 116) := by
  intro τ hτ
  rcases hτ with ⟨⟨hvle, hn, hL, halen, hactive, hord, hkeys, hinp⟩, hvn⟩
  have hvB : τ.vars "v" < B := hvn.trans hnB
  have halen_le_v : τ.vars "alen" ≤ τ.vars "v" := by
    rw [halen]
    exact scanList_length_le active 0 (τ.vars "v")
  have halenB : τ.vars "alen" < B := lt_of_le_of_lt halen_le_v hvB
  have halen_n : τ.vars "alen" < n := halen_le_v.trans_lt hvn
  have halen_succB : τ.vars "alen" + 1 < B := by omega
  have hv_succB : τ.vars "v" + 1 < B := by omega
  have hactiveGet : (τ.arrs "activeA")[τ.vars "v"]? =
      some (active (τ.vars "v")) := by
    rw [hactive]
    exact getElem?_arrOf active hvn
  have hgetEval : (Expr.get "activeA" (.var "v")).evalB B τ =
      some (active (τ.vars "v")) :=
    evalB_get (evalB_var hvB) hactiveGet (hactiveB _ hvn)
  let test := Cond.eq (.get "activeA" (.var "v")) (.lit 1)
  by_cases hav : active (τ.vars "v") = 1
  · have htest : test.evalB B τ = some true := by
      simpa [test, hav] using evalB_condEq hgetEval (evalB_lit (by omega : 1 < B))
    let τ₁ := τ.setArr "ord" (τ.vars "alen") (τ.vars "v")
    have rstore : Run B (.store "ord" (.var "alen") (.var "v")) τ τ₁ 3 := by
      exact Run.store (evalB_var halenB) (evalB_var hvB)
        (by rw [hord.length]; exact halen_n)
    have hkeys₁ : ∀ d, τ₁.arrs (keyName d) =
        arrOf n (filledKey original active bits (τ.vars "v") d) := by
      intro d
      rw [show τ₁.arrs (keyName d) = τ.arrs (keyName d) by
        simp [τ₁, keyName_ne_ord d]]
      exact hkeys d
    have hv₁ : τ₁.vars "v" = τ.vars "v" := by simp [τ₁]
    have hL₁ : τ₁.vars "L" = L := by simp [τ₁, hL]
    have hremain := scanList_remaining (active := active) hvn
    have hinp₁ : τ₁.inp = joined8 (bits (τ.vars "v")) ++
        (keyTape bits (scanList active (τ.vars "v" + 1)
          (n - (τ.vars "v" + 1))) ++ rest) := by
      rw [show τ₁.inp = τ.inp by simp [τ₁], hinp, hremain, if_pos hav]
      simp [keyTape, List.append_assoc]
    obtain ⟨τ₂, rkeys, hkeys₂, hinp₂, hv₂, hL₂⟩ :=
      readAllKeyDigits_run
        (g := fun d => filledKey original active bits (τ.vars "v") d)
        (b := bits (τ.vars "v")) hkeys₁ hv₁ hvn hL₁
        (hlen _ hvn) (hbits _ hvn) hinp₁ hpowB hnB htwoB
    let τ₃ := τ₂.setVar "alen" (τ.vars "alen" + 1)
    have halen₂ : τ₂.vars "alen" = τ.vars "alen" := by
      rw [rkeys.frame_var "alen" (by decide)]
      simp [τ₁]
    have ralen : Run B (inc "alen") τ₂ τ₃ 4 := by
      apply Run.assign
      apply evalB_bin
      · rw [evalB_var_iff]
        exact ⟨halen₂.symm, by rw [halen₂]; exact halenB⟩
      · exact evalB_lit (by omega)
      · exact halen_succB
    let τ₄ := τ₃.setVar "v" (τ.vars "v" + 1)
    have hv₃ : τ₃.vars "v" = τ.vars "v" := by simp [τ₃, hv₂]
    have rv : Run B (inc "v") τ₃ τ₄ 4 := by
      apply Run.assign
      apply evalB_bin
      · rw [evalB_var_iff]
        exact ⟨hv₃.symm, by rw [hv₃]; exact hvB⟩
      · exact evalB_lit (by omega)
      · exact hv_succB
    have rbranch : Run B
        (seqs [.store "ord" (.var "alen") (.var "v"),
          readAllKeyDigits, inc "alen"]) τ τ₃ (120 * L + 95) := by
      simpa [seqs] using (rstore.seq (rkeys.seq ralen)).mono (by omega)
    have rr : Run B
        (seqs [
          .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
            (seqs [.store "ord" (.var "alen") (.var "v"),
              readAllKeyDigits, inc "alen"])
            .skip,
          inc "v"]) τ τ₄ (120 * L + 116) := by
      exact (Run.seq (Run.ite_true htest rbranch) rv).mono (by
        simp [test]
        omega)
    refine ⟨τ₄, rr, ?_, by simp [τ₄, τ₃]⟩
    have hprefix : (scanList active 0 (τ.vars "v" + 1)).length =
        τ.vars "alen" + 1 := by
      rw [scanList_zero_add, if_pos hav, List.length_append, halen]
      simp
    have hordStep := hord.step halen_n
      (show τ.vars "v" = (scanList active 0 n).getD (τ.vars "alen") 0 by
        rw [halen]
        exact (scanList_active_getD hvn hav).symm)
    have hord₄ : Fill.Below "ord" "alen" n
        (fun i => (scanList active 0 n).getD i 0) τ₄ := by
      apply hordStep.of_eq
      · simp [τ₄, τ₃, rkeys.frame_arr "ord" (by decide), τ₁]
      · simp [τ₄, τ₃]
    refine ⟨by simp [τ₄, τ₃]; omega, by
        rw [show τ₄.vars "n" = τ.vars "n" by
          simp [τ₄, τ₃, rkeys.frame_var "n" (by decide), τ₁]]
        exact hn,
      by simp [τ₄, τ₃, hL₂], by simpa [τ₄, τ₃] using hprefix.symm, ?_, hord₄,
      ?_, ?_⟩
    · rw [show τ₄.arrs "activeA" = τ.arrs "activeA" by
          simp [τ₄, τ₃, rkeys.frame_arr "activeA" (by decide), τ₁]]
      exact hactive
    · intro d
      rw [show τ₄.arrs (keyName d) = τ₂.arrs (keyName d) by simp [τ₄, τ₃],
        hkeys₂ d, updateKeys_filledKey_succ hav d]
      simp [τ₄, τ₃]
    · simpa [τ₄, τ₃] using hinp₂
  · have htest : test.evalB B τ = some false := by
      simpa [test, hav] using evalB_condEq hgetEval (evalB_lit (by omega : 1 < B))
    let τ₁ := τ.setVar "v" (τ.vars "v" + 1)
    have rv : Run B (inc "v") τ τ₁ 4 := by
      apply Run.assign
      exact evalB_bin (evalB_var hvB) (evalB_lit (by omega)) hv_succB
    have rr : Run B
        (seqs [
          .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
            (seqs [.store "ord" (.var "alen") (.var "v"),
              readAllKeyDigits, inc "alen"])
            .skip,
          inc "v"]) τ τ₁ (120 * L + 116) := by
      exact (Run.seq (Run.ite_false htest Run.skip) rv).mono (by
        simp [test])
    refine ⟨τ₁, rr, ?_, by simp [τ₁]⟩
    have hprefix : (scanList active 0 (τ.vars "v" + 1)).length =
        τ.vars "alen" := by
      rw [scanList_zero_add, if_neg hav, List.append_nil, halen]
    have hremaining : scanList active (τ.vars "v") (n - τ.vars "v") =
        scanList active (τ.vars "v" + 1) (n - (τ.vars "v" + 1)) := by
      rw [scanList_remaining hvn, if_neg hav]
    have hv₁ : τ₁.vars "v" = τ.vars "v" + 1 := by simp [τ₁]
    refine ⟨by simp [τ₁]; omega, by simp [τ₁, hn], by simp [τ₁, hL],
      by simpa [τ₁] using hprefix.symm, by simp [τ₁, hactive], ?_, ?_, ?_⟩
    · exact hord.of_eq (by simp [τ₁]) (by simp [τ₁])
    · intro d
      rw [show τ₁.arrs (keyName d) = τ.arrs (keyName d) by simp [τ₁],
        hkeys d, hv₁, filledKey_succ_of_inactive hav d]
    · rw [show τ₁.inp = τ.inp by simp [τ₁], hinp, hremaining, hv₁]

/-- `readKeys` consumes exactly the active vertices' key blocks, writes
their increasing enumeration to `ord`, and records every decoded digit. -/
theorem readKeys_run {B n L : ℕ} {σ : Env} {active ord : ℕ → ℕ}
    {original : Fin 8 → ℕ → ℕ} {bits : ℕ → Fin 8 → List ℕ}
    {rest : List ℕ}
    (hn : σ.vars "n" = n) (hL : σ.vars "L" = L)
    (hactive : σ.arrs "activeA" = arrOf n active)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hkeys : ∀ d, σ.arrs (keyName d) = arrOf n (original d))
    (hinp : σ.inp = keyTape bits (scanList active 0 n) ++ rest)
    (hlen : ∀ v < n, ∀ d, (bits v d).length = L)
    (hbits : ∀ v < n, ∀ d x, x ∈ bits v d → x ≤ 1)
    (hactiveB : ∀ v < n, active v < B)
    (hpowB : 2 ^ L < B) (hnB : n < B) (htwoB : 2 < B) :
    ∃ σ' ord', Run B readKeys σ σ'
        ((120 * L + 120) * n + 8) ∧
      σ'.vars "alen" = (scanList active 0 n).length ∧
      σ'.vars "v" = n ∧ σ'.vars "n" = n ∧ σ'.vars "L" = L ∧
      σ'.arrs "ord" = arrOf n ord' ∧
      (∀ i < (scanList active 0 n).length,
        ord' i = (scanList active 0 n).getD i 0) ∧
      (∀ d, σ'.arrs (keyName d) =
        arrOf n (filledKey original active bits n d)) ∧
      σ'.inp = rest := by
  let σ₀ := σ.setVar "alen" 0
  have r₀ : Run B (.assign "alen" (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  have hI₀ : ReadKeysInv n L active original bits rest (σ₀.setVar "v" 0) := by
    refine ⟨by simp, by simp [σ₀, hn], by simp [σ₀, hL], by simp [σ₀, scanList],
      by simp [σ₀, hactive], ?_, ?_, ?_⟩
    · exact Fill.below_zero (g := ord) (by simp [σ₀, hord]) (by rfl)
    · intro d
      have hvzero : (σ₀.setVar "v" 0).vars "v" = 0 := by simp
      rw [show (σ₀.setVar "v" 0).arrs (keyName d) = σ.arrs (keyName d) by
          simp [σ₀], hkeys d, hvzero]
      apply arrOf_congr
      intro i hi
      simp [filledKey]
    · simpa [σ₀, scanList] using hinp
  have hloop := Spec.forRangeZero (B := B) "v" "n"
    (ReadKeysInv n L active original bits rest) n (120 * L + 116) hnB
    (fun _ h => h.1) (fun _ h => h.2.1)
    (readKeys_body_spec hlen hbits hactiveB hpowB hnB htwoB)
  obtain ⟨σ', rloop, hI', hv'⟩ := hloop.run hI₀
  rcases hI' with ⟨-, hn', hL', halen', -, hord', hkeys', hinp'⟩
  have halenFinal : σ'.vars "alen" = (scanList active 0 n).length := by
    simpa [hv'] using halen'
  obtain ⟨ord', hordFill⟩ := hord'
  have hordval : ∀ i < (scanList active 0 n).length,
      ord' i = (scanList active 0 n).getD i 0 := by
    intro i hi
    apply hordFill.cell
    rwa [halenFinal]
  have hkeysFinal : ∀ d, σ'.arrs (keyName d) =
      arrOf n (filledKey original active bits n d) := by
    intro d
    simpa [hv'] using hkeys' d
  refine ⟨σ', ord', ?_, halenFinal, hv', hn', hL', hordFill.arr, hordval,
    hkeysFinal, ?_⟩
  · have rr := r₀.seq rloop
    have hcost : 2 + ((120 * L + 116 + 4) * n + 6) =
        (120 * L + 120) * n + 8 := by ring
    rw [← hcost]
    simpa [readKeys, seqs] using rr
  · simpa [hv', scanList] using hinp'

end Lax235315Proofs.Construction.ReadKeys
