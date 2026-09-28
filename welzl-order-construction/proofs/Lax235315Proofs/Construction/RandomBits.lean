import Lax235315Proofs.Construction.WelzlProgram
import Lax808846Proofs.Spec
import Mathlib.Tactic

/-! Source semantics for the binary random-key reader. -/

namespace Lax235315Proofs.Construction.RandomBits

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram

/-- Most-significant-bit-first value of a word list. -/
def bitsValue (xs : List ℕ) : ℕ :=
  xs.foldl (fun a b => 2 * a + b) 0

@[simp] lemma bitsValue_nil : bitsValue [] = 0 := rfl

lemma bitsValue_append (xs : List ℕ) (b : ℕ) :
    bitsValue (xs ++ [b]) = 2 * bitsValue xs + b := by
  simp [bitsValue, List.foldl_append]

lemma bitsValue_lt_pow (xs : List ℕ)
    (hbits : ∀ b ∈ xs, b ≤ 1) : bitsValue xs < 2 ^ xs.length := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs b ih =>
      have hb : b ≤ 1 := hbits b (by simp)
      have hxs : ∀ a ∈ xs, a ≤ 1 := by
        intro a ha
        exact hbits a (by simp [ha])
      rw [bitsValue_append, List.length_append, List.length_singleton,
        Nat.pow_succ]
      have := ih hxs
      omega

lemma bitsValue_take_succ {xs : List ℕ} {i : ℕ} (hi : i < xs.length) :
    bitsValue (xs.take (i + 1)) =
      2 * bitsValue (xs.take i) + xs.getD i 0 := by
  rw [List.take_succ_eq_append_getElem hi, bitsValue_append]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

def ReadDigitInv (key : String) (v L : ℕ) (bs rest : List ℕ)
    (original : List ℕ) (τ : Env) : Prop :=
  τ.vars "v" = v ∧ τ.vars "L" = L ∧ τ.vars "j" ≤ L ∧
    τ.vars "digit" = bitsValue (bs.take (τ.vars "j")) ∧
    τ.inp = bs.drop (τ.vars "j") ++ rest ∧ τ.arrs key = original

/-- One key digit is read exactly, as a binary number, into the selected
vertex cell. -/
lemma readKeyDigit_run {B n v L : ℕ} {key : String}
    {σ : Env} {g : ℕ → ℕ} {bs rest : List ℕ}
    (hkey : σ.arrs key = arrOf n g)
    (hv : σ.vars "v" = v) (hvn : v < n)
    (hL : σ.vars "L" = L) (hbs : bs.length = L)
    (hinp : σ.inp = bs ++ rest)
    (hbits : ∀ b ∈ bs, b ≤ 1)
    (hpowB : 2 ^ L < B) (hnB : n < B) (htwoB : 2 < B) :
    ∃ σ' g', Run B (readKeyDigit key) σ σ' (15 * L + 11) ∧
      σ'.arrs key = arrOf n g' ∧ g' v = bitsValue bs ∧
      (∀ i < n, i ≠ v → g' i = g i) ∧ σ'.inp = rest ∧
      σ'.vars "v" = v ∧ σ'.vars "L" = L := by
  let original := arrOf n g
  let body : Com := seqs [
    .read "bit",
    .assign "digit" (.add (.mul (.var "digit") (.lit 2)) (.var "bit")),
    inc "j"]
  have hbody : Spec B
      (fun τ => ReadDigitInv key v L bs rest original τ ∧ τ.vars "j" < L)
      body
      (fun τ τ' => ReadDigitInv key v L bs rest original τ' ∧
        τ'.vars "j" = τ.vars "j" + 1) 11 := by
    rintro τ ⟨⟨hvτ, hLτ, hjle, hdigit, hinpτ, hkeyτ⟩, hjlt⟩
    have hjlen : τ.vars "j" < bs.length := by omega
    let b := bs.getD (τ.vars "j") 0
    have hbmem : b ∈ bs := by
      simp [b, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjlen,
        List.getElem_mem hjlen]
    have hb1 : b ≤ 1 := hbits b hbmem
    have hbB : b < B := by omega
    have hhead : τ.inp = b :: (bs.drop (τ.vars "j" + 1) ++ rest) := by
      calc
        τ.inp = bs.drop (τ.vars "j") ++ rest := hinpτ
        _ = bs[τ.vars "j"] :: (bs.drop (τ.vars "j" + 1) ++ rest) := by
          rw [List.drop_eq_getElem_cons hjlen, List.cons_append]
        _ = b :: (bs.drop (τ.vars "j" + 1) ++ rest) := by
          congr 1
          simp [b, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hjlen]
    have hprefixBits : ∀ a ∈ bs.take (τ.vars "j"), a ≤ 1 := by
      intro a ha
      exact hbits a (List.mem_of_mem_take ha)
    have hdigitLt : τ.vars "digit" < 2 ^ τ.vars "j" := by
      rw [hdigit]
      have ht := bitsValue_lt_pow _ hprefixBits
      rw [List.length_take, Nat.min_eq_left (by omega)] at ht
      exact ht
    have hpowj : 2 ^ τ.vars "j" ≤ 2 ^ L :=
      Nat.pow_le_pow_right (by omega) hjle
    have hdigitB : τ.vars "digit" < B :=
      lt_of_lt_of_le hdigitLt (hpowj.trans hpowB.le)
    have hmulB : τ.vars "digit" * 2 < B := by
      have hnext : τ.vars "digit" * 2 < 2 ^ (τ.vars "j" + 1) := by
        rw [Nat.pow_succ]
        omega
      exact lt_of_lt_of_le hnext
        ((Nat.pow_le_pow_right (by omega) (by omega)).trans hpowB.le)
    have hnextB : τ.vars "digit" * 2 + b < B := by
      have hnext : τ.vars "digit" * 2 + b < 2 ^ (τ.vars "j" + 1) := by
        rw [Nat.pow_succ]
        omega
      exact lt_of_lt_of_le hnext
        ((Nat.pow_le_pow_right (by omega) (by omega)).trans hpowB.le)
    have hjB : τ.vars "j" < B := by
      have : τ.vars "j" < 2 ^ τ.vars "j" := Nat.lt_two_pow_self
      exact lt_of_lt_of_le this (hpowj.trans hpowB.le)
    have hj1B : τ.vars "j" + 1 < B := by
      exact lt_of_le_of_lt (by omega : τ.vars "j" + 1 ≤ L)
        (lt_of_lt_of_le Nat.lt_two_pow_self hpowB.le)
    let τ₁ := { τ.setVar "bit" b with
      inp := bs.drop (τ.vars "j" + 1) ++ rest }
    let τ₂ := τ₁.setVar "digit" (τ.vars "digit" * 2 + b)
    let τ₃ := τ₂.setVar "j" (τ.vars "j" + 1)
    have r₁ : Run B (.read "bit") τ τ₁ 1 := by
      exact Run.read hhead
    have r₂ : Run B
        (.assign "digit" (.add (.mul (.var "digit") (.lit 2)) (.var "bit")))
        τ₁ τ₂ 6 := by
      apply Run.assign
      apply evalB_bin
      · exact evalB_bin (evalB_var (by simpa [τ₁] using hdigitB))
          (evalB_lit htwoB) hmulB
      · exact evalB_var (by simpa [τ₁] using hbB)
      · exact hnextB
    have r₃ : Run B (inc "j") τ₂ τ₃ 4 := by
      apply Run.assign
      exact evalB_bin (evalB_var (by simpa [τ₂, τ₁] using hjB))
        (evalB_lit (by omega)) (by simpa [τ₂, τ₁] using hj1B)
    refine ⟨τ₃, ?_, ?_⟩
    · simpa [body, seqs] using r₁.seq (r₂.seq r₃)
    · constructor
      · refine ⟨by simp [τ₃, τ₂, τ₁, hvτ],
          by simp [τ₃, τ₂, τ₁, hLτ], by simp [τ₃, τ₂, τ₁]; omega, ?_,
          by simp [τ₃, τ₂, τ₁], by simp [τ₃, τ₂, τ₁, hkeyτ]⟩
        change τ.vars "digit" * 2 + b =
          bitsValue (bs.take (τ.vars "j" + 1))
        rw [bitsValue_take_succ hjlen, ← hdigit]
        omega
      · simp [τ₃, τ₂, τ₁]
  have hloop : Spec B
      (ReadDigitInv key v L bs rest original)
      (.while (.lt (.var "j") (.var "L")) body)
      (fun _ τ => ReadDigitInv key v L bs rest original τ ∧
        (Cond.lt (.var "j") (.var "L")).evalB B τ = some false)
      (15 * L + 4) := by
    apply Spec.while_count (I := ReadDigitInv key v L bs rest original)
      (V := fun τ => L - τ.vars "j") (Kb := 11)
    · intro τ hτ
      apply evalB_condLt_vars
      · have : τ.vars "j" ≤ L := hτ.2.2.1
        exact lt_of_le_of_lt this
          (lt_of_lt_of_le Nat.lt_two_pow_self hpowB.le)
      · rw [hτ.2.1]
        exact lt_of_lt_of_le Nat.lt_two_pow_self hpowB.le
    · apply hbody.conseq
      · intro τ hτ
        refine ⟨hτ.1, ?_⟩
        have hjlt' := lt_of_condLt_true hτ.2
        rw [hτ.1.2.1] at hjlt'
        exact hjlt'
      · intro τ τ' hτ hpost
        refine ⟨hpost.1, ?_⟩
        have hjlt' := lt_of_condLt_true hτ.2
        rw [hτ.1.2.1] at hjlt'
        rw [hpost.2]
        omega
      · exact le_rfl
    · exact fun _ h => h
    · intro τ hτ
      dsimp
      omega
  let σ₀ := σ.setVar "digit" 0
  let σ₁ := σ₀.setVar "j" 0
  have r₀ : Run B (.assign "digit" (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  have rinit : Run B (.assign "j" (.lit 0)) σ₀ σ₁ 2 :=
    Run.assign (evalB_lit (by omega))
  have hI : ReadDigitInv key v L bs rest original σ₁ := by
    simp [ReadDigitInv, σ₁, σ₀, hv, hL, hinp, original, hkey]
  obtain ⟨σ₂, rloop, hI₂, hjfalse⟩ := hloop.run hI
  have hjL : σ₂.vars "j" = L := by
    have hLle := le_of_condLt_false hjfalse
    rw [hI₂.2.1] at hLle
    exact le_antisymm hI₂.2.2.1 hLle
  have hdigit₂ : σ₂.vars "digit" = bitsValue bs := by
    rw [hI₂.2.2.2.1, hjL, ← hbs, List.take_length]
  have hv₂ : σ₂.vars "v" = v := hI₂.1
  have harr₂ : σ₂.arrs key = arrOf n g := by
    simpa [original] using hI₂.2.2.2.2.2
  have hindex : σ₂.vars "v" < (σ₂.arrs key).length := by
    rw [harr₂, length_arrOf, hv₂]
    exact hvn
  have hvB : σ₂.vars "v" < B := by rw [hv₂]; exact hvn.trans hnB
  have hdigitB : σ₂.vars "digit" < B := by
    rw [hdigit₂]
    exact lt_of_lt_of_le (bitsValue_lt_pow bs hbits) (by simpa [hbs] using hpowB.le)
  let σ₃ := σ₂.setArr key v (bitsValue bs)
  have rstore : Run B (.store key (.var "v") (.var "digit")) σ₂ σ₃ 3 := by
    simpa [σ₃, hv₂, hdigit₂] using
      (Run.store (evalB_var hvB) (evalB_var hdigitB) hindex)
  let g' := fun i => if i = v then bitsValue bs else g i
  refine ⟨σ₃, g', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have rr := r₀.seq (rinit.seq (rloop.seq rstore))
    simpa [readKeyDigit, body, seqs] using rr.mono (by omega)
  · simp [σ₃, harr₂, set_arrOf, g']
  · simp [g']
  · intro i hi hiv
    simp [g', hiv]
  · simp [σ₃]
    rw [hI₂.2.2.2.2.1, hjL, ← hbs, List.drop_length]
    simp
  · simpa [σ₃] using hv₂
  · simpa [σ₃] using hI₂.2.1

end Lax235315Proofs.Construction.RandomBits
