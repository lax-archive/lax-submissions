import Lax235315Proofs.Construction.RadixPass
import Lax235315Proofs.Construction.RandomKeysRead
import Mathlib.Tactic

/-! Composition of the eight least-significant-first radix passes. -/

namespace Lax235315Proofs.Construction.RadixEight

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.RadixPass
open Lax235315Proofs.Construction.RandomKeysRead
open Lax235315Proofs.Construction.WelzlProgram

theorem bigStep_array_length_eq {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStep c σ σ' k) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  induction h <;> simp_all [Env.setArr] <;> split_ifs <;> simp_all

theorem run_array_length_eq {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ}
    (h : Run B c σ σ' K) (a : String) :
    (σ'.arrs a).length = (σ.arrs a).length := by
  obtain ⟨_, _, hb⟩ := h.bigStep
  exact bigStep_array_length_eq hb a

theorem exists_arrOf_of_length {l : List ℕ} {n : ℕ} (h : l.length = n) :
    ∃ f : ℕ → ℕ, l = arrOf n f := by
  let f := fun i => l.getD i 0
  refine ⟨f, ?_⟩
  apply List.ext_getElem
  · simp [h]
  · intro i hi hi'
    simp only [f, arrOf]
    rw [List.getElem_map, List.getElem_range]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

def SortState (n q : ℕ) (digits : Fin 8 → ℕ → ℕ)
    (xs : List ℕ) (τ : Env) : Prop :=
  τ.vars "alen" = xs.length ∧ τ.vars "qpow" = q ∧
    (∃ ord, τ.arrs "ord" = arrOf n ord ∧
      ∀ i < xs.length, ord i = xs.getD i 0) ∧
    (∀ d, τ.arrs (keyName d) = arrOf n (digits d)) ∧
    (∃ count, τ.arrs "count" = arrOf q count) ∧
    ∃ scratch, τ.arrs "scratchOrder" = arrOf n scratch

private theorem keyName_ne_ord (d : Fin 8) : keyName d ≠ "ord" := by
  fin_cases d <;> decide

private theorem keyName_ne_count (d : Fin 8) : keyName d ≠ "count" := by
  fin_cases d <;> decide

private theorem keyName_ne_scratch (d : Fin 8) : keyName d ≠ "scratchOrder" := by
  fin_cases d <;> decide

private theorem radixPass_preserves_keys {B : ℕ} {d : Fin 8} {σ σ' : Env}
    {K : ℕ} (r : Run B (radixPass (keyName d)) σ σ' K)
    (e : Fin 8) : σ'.arrs (keyName e) = σ.arrs (keyName e) := by
  apply r.frame_arr
  fin_cases d <;> fin_cases e <;>
    decide

theorem onePass_run {B n q : ℕ} {digits : Fin 8 → ℕ → ℕ}
    {xs : List ℕ} {d : Fin 8} {σ : Env}
    (hstate : SortState n q digits xs σ)
    (hxn : xs.length ≤ n) (hnB : n < B) (hqB : q < B)
    (hxs : xs.Nodup) (hvert : ∀ x ∈ xs, x < n)
    (hkey : ∀ e x, x ∈ xs → digits e x < q) :
    ∃ σ', Run B (radixPass (keyName d)) σ σ'
        (64 * (xs.length + q + 1)) ∧
      SortState n q digits (bucketSort q (digits d) xs) σ' := by
  rcases hstate with ⟨halen, hqpow, ⟨ord, hord, hordval⟩, hkeys,
    ⟨count, hcount⟩, scratch, hscratch⟩
  obtain ⟨σ', ord', r, halen', hqpow', hord', hordval', hkeyd'⟩ :=
    radixPass_run halen hqpow hord hordval (hkeys d) hcount hscratch
      (keyName_ne_ord d) (keyName_ne_count d) (keyName_ne_scratch d)
      hxn hnB hqB hxs hvert (hkey d)
  have hp := bucketSort_perm hxs (hkey d)
  have hlen : (bucketSort q (digits d) xs).length = xs.length := hp.length_eq
  have hcountLen : (σ'.arrs "count").length = q := by
    rw [run_array_length_eq r "count", hcount, length_arrOf]
  obtain ⟨count', hcount'⟩ := exists_arrOf_of_length hcountLen
  have hscratchLen : (σ'.arrs "scratchOrder").length = n := by
    rw [run_array_length_eq r "scratchOrder", hscratch, length_arrOf]
  obtain ⟨scratch', hscratch'⟩ := exists_arrOf_of_length hscratchLen
  have hordvalNew : ∀ i < (bucketSort q (digits d) xs).length,
      ord' i = (bucketSort q (digits d) xs).getD i 0 := by
    intro i hi
    apply hordval' i
    simpa [hlen] using hi
  refine ⟨σ', r, ?_⟩
  refine ⟨by simpa [hlen] using halen', hqpow', ⟨ord', hord', hordvalNew⟩, ?_,
    ⟨count', hcount'⟩, scratch', hscratch'⟩
  intro e
  rw [radixPass_preserves_keys r e, hkeys e]

private theorem pass_mem {q : ℕ} {digits : Fin 8 → ℕ → ℕ}
    {xs : List ℕ} (hkey : ∀ e x, x ∈ xs → digits e x < q)
    (d : Fin 8) {x : ℕ} (hx : x ∈ bucketSort q (digits d) xs) : x ∈ xs :=
  (mem_bucketSort.mp hx).1

private theorem pass_properties {n q : ℕ}
    {digits : Fin 8 → ℕ → ℕ} {xs : List ℕ}
    (hxs : xs.Nodup) (hvert : ∀ x ∈ xs, x < n)
    (hkey : ∀ e x, x ∈ xs → digits e x < q) (d : Fin 8) :
    (bucketSort q (digits d) xs).Nodup ∧
      (∀ x ∈ bucketSort q (digits d) xs, x < n) ∧
      ∀ e x, x ∈ bucketSort q (digits d) xs → digits e x < q := by
  refine ⟨nodup_bucketSort hxs, ?_, ?_⟩
  · intro x hx
    exact hvert x (pass_mem hkey d hx)
  · intro e x hx
    exact hkey e x (pass_mem hkey d hx)

/-- The fixed sequence in `reductionRound` implements all eight stable
least-significant-first passes. -/
theorem radixEight_run {B n q : ℕ} {digits : Fin 8 → ℕ → ℕ}
    {xs : List ℕ} {σ : Env}
    (hstate : SortState n q digits xs σ)
    (hxn : xs.length ≤ n) (hnB : n < B) (hqB : q < B)
    (hxs : xs.Nodup) (hvert : ∀ x ∈ xs, x < n)
    (hkey : ∀ d x, x ∈ xs → digits d x < q) :
    ∃ σ', Run B (seqs ((keyNames.reverse).map radixPass)) σ σ'
        (512 * (xs.length + q + 1)) ∧
      SortState n q digits (radixSort8 q digits xs) σ' := by
  let x₇ := bucketSort q (digits 7) xs
  let x₆ := bucketSort q (digits 6) x₇
  let x₅ := bucketSort q (digits 5) x₆
  let x₄ := bucketSort q (digits 4) x₅
  let x₃ := bucketSort q (digits 3) x₄
  let x₂ := bucketSort q (digits 2) x₃
  let x₁ := bucketSort q (digits 1) x₂
  let x₀ := bucketSort q (digits 0) x₁
  obtain ⟨σ₇, r₇, s₇⟩ := onePass_run (d := (7 : Fin 8)) hstate
    hxn hnB hqB hxs hvert hkey
  obtain ⟨nd₇, vert₇, key₇⟩ := pass_properties hxs hvert hkey (7 : Fin 8)
  have len₇ : x₇.length = xs.length :=
    (bucketSort_perm hxs (hkey 7)).length_eq
  obtain ⟨σ₆, r₆, s₆⟩ := onePass_run (d := (6 : Fin 8)) s₇
    (by change x₇.length ≤ n; rw [len₇]; exact hxn) hnB hqB nd₇ vert₇ key₇
  obtain ⟨nd₆, vert₆, key₆⟩ := pass_properties nd₇ vert₇ key₇ (6 : Fin 8)
  have len₆ : x₆.length = x₇.length :=
    (bucketSort_perm nd₇ (key₇ 6)).length_eq
  obtain ⟨σ₅, r₅, s₅⟩ := onePass_run (d := (5 : Fin 8)) s₆
    (by change x₆.length ≤ n; rw [len₆, len₇]; exact hxn)
      hnB hqB nd₆ vert₆ key₆
  obtain ⟨nd₅, vert₅, key₅⟩ := pass_properties nd₆ vert₆ key₆ (5 : Fin 8)
  have len₅ : x₅.length = x₆.length :=
    (bucketSort_perm nd₆ (key₆ 5)).length_eq
  obtain ⟨σ₄, r₄, s₄⟩ := onePass_run (d := (4 : Fin 8)) s₅
    (by change x₅.length ≤ n; rw [len₅, len₆, len₇]; exact hxn)
      hnB hqB nd₅ vert₅ key₅
  obtain ⟨nd₄, vert₄, key₄⟩ := pass_properties nd₅ vert₅ key₅ (4 : Fin 8)
  have len₄ : x₄.length = x₅.length :=
    (bucketSort_perm nd₅ (key₅ 4)).length_eq
  obtain ⟨σ₃, r₃, s₃⟩ := onePass_run (d := (3 : Fin 8)) s₄
    (by change x₄.length ≤ n; rw [len₄, len₅, len₆, len₇]; exact hxn)
      hnB hqB nd₄ vert₄ key₄
  obtain ⟨nd₃, vert₃, key₃⟩ := pass_properties nd₄ vert₄ key₄ (3 : Fin 8)
  have len₃ : x₃.length = x₄.length :=
    (bucketSort_perm nd₄ (key₄ 3)).length_eq
  obtain ⟨σ₂, r₂, s₂⟩ := onePass_run (d := (2 : Fin 8)) s₃
    (by change x₃.length ≤ n; rw [len₃, len₄, len₅, len₆, len₇]; exact hxn)
      hnB hqB nd₃ vert₃ key₃
  obtain ⟨nd₂, vert₂, key₂⟩ := pass_properties nd₃ vert₃ key₃ (2 : Fin 8)
  have len₂ : x₂.length = x₃.length :=
    (bucketSort_perm nd₃ (key₃ 2)).length_eq
  obtain ⟨σ₁, r₁, s₁⟩ := onePass_run (d := (1 : Fin 8)) s₂
    (by change x₂.length ≤ n; rw [len₂, len₃, len₄, len₅, len₆, len₇]; exact hxn)
      hnB hqB nd₂ vert₂ key₂
  obtain ⟨nd₁, vert₁, key₁⟩ := pass_properties nd₂ vert₂ key₂ (1 : Fin 8)
  have len₁ : x₁.length = x₂.length :=
    (bucketSort_perm nd₂ (key₂ 1)).length_eq
  obtain ⟨σ₀, r₀, s₀⟩ := onePass_run (d := (0 : Fin 8)) s₁
    (by change x₁.length ≤ n; rw [len₁, len₂, len₃, len₄, len₅, len₆, len₇]; exact hxn)
      hnB hqB nd₁ vert₁ key₁
  refine ⟨σ₀, ?_, ?_⟩
  · have rr := r₇.seq (r₆.seq (r₅.seq (r₄.seq (r₃.seq (r₂.seq (r₁.seq r₀))))))
    have rb : Run B _ σ σ₀ (512 * (xs.length + q + 1)) :=
      rr.mono (by simp only [x₇, x₆, x₅, x₄, x₃, x₂, x₁] at *; omega)
    simpa [keyNames, keyName, seqs] using rb
  · simpa [radixSort8, x₇, x₆, x₅, x₄, x₃, x₂, x₁, x₀] using s₀

end Lax235315Proofs.Construction.RadixEight
