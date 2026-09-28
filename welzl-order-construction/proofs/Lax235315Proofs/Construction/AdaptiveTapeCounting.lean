import Lax235315Proofs.Construction.AdaptiveBitBlocks
import Mathlib.Tactic

set_option maxHeartbeats 500000

/-!
Finite-tape interpretation of `AdaptiveBitBlocks.failureMass`. Blocks are
split from the front of a fixed tape, and any suffix unused by a stopped
execution is ignored. The tape length need only dominate the maximum path
consumption, so block widths can vary with the observed prefixes.
-/

namespace Lax235315Proofs.Construction.AdaptiveTapeCounting

open Lax235315Proofs.Construction.AdaptiveBitBlocks

/-- Boolean tapes of a fixed finite length. -/
abbrev Tape (T : ℕ) := Fin T → Bool

/-- Split a fixed tape into a prefix and its remaining suffix. -/
def splitEquiv {k T : ℕ} (hk : k ≤ T) : Tape T ≃ Tape k × Tape (T - k) := by
  let h := Nat.add_sub_of_le hk
  refine
    { toFun := fun tape =>
        ((fun i => tape (Fin.cast h (Fin.castAdd (T - k) i))),
         (fun j => tape (Fin.cast h (Fin.natAdd k j))) )
      invFun := fun parts => Fin.addCases parts.1 parts.2 ∘ Fin.cast h.symm
      left_inv := ?_
      right_inv := ?_ }
  · intro tape
    funext i
    have hsplit := Fin.addCases_castAdd_natAdd
      (v := fun j => tape (Fin.cast h j)) (Fin.cast h.symm i)
    simpa [Function.comp_apply] using hsplit
  · intro parts
    rcases parts with ⟨head, suffix⟩
    apply Prod.ext
    · funext i
      simp [Function.comp_apply]
    · funext i
      simp [Function.comp_apply]

/-- A protocol fits in `T` bits when every possible continuation fits in
the suffix left after the current query. -/
def Fits : {R : ℕ} → Protocol R → ℕ → Prop
  | _, .stop _, _ => True
  | _, .query (k := k) _ next, T =>
      k ≤ T ∧ ∀ bits, Fits (next bits) (T - k)

/-- Every protocol fits in any tape at least as long as its maximum path
consumption. -/
lemma fits_of_maxConsumedBits {R : ℕ} (p : Protocol R) (T : ℕ)
    (hT : maxConsumedBits p ≤ T) : Fits p T := by
  induction p generalizing T with
  | stop _ => trivial
  | @query r k bad next ih =>
      simp only [maxConsumedBits] at hT
      constructor
      · omega
      · intro bits
        have hbits : maxConsumedBits (next bits) ≤
            Finset.univ.sup (fun x : Fin k → Bool => maxConsumedBits (next x)) :=
          Finset.le_sup (s := Finset.univ)
            (f := fun x : Fin k → Bool => maxConsumedBits (next x)) (Finset.mem_univ bits)
        apply ih bits
        omega

/-- The failing fixed tapes. At a bad prefix every remaining suffix is
counted; at a good prefix the recursive failure set is used. -/
noncomputable def failingTapes : {R : ℕ} → (p : Protocol R) →
    (T : ℕ) → Fits p T → Finset (Tape T)
  | _, .stop _, _, _ => ∅
  | _, .query (k := k) bad next, T, hfit => by
      classical
      rcases hfit with ⟨hk, hnext⟩
      exact (Finset.univ : Finset (Tape k)).biUnion fun bits =>
        (if bits ∈ bad then (Finset.univ : Finset (Tape (T - k)))
         else failingTapes (next bits) (T - k) (hnext bits)).image
        (fun suffix => (splitEquiv hk).symm (bits, suffix))

/-- A fixed tape space of length `T` has `2^T` members. -/
lemma card_tape (T : ℕ) : Fintype.card (Tape T) = 2 ^ T := by
  simp [Tape]

/-- The finite first-block decomposition of the failing-tape set. -/
lemma card_failingTapes_query {R k T : ℕ}
    (bad : Finset (Tape k)) (next : Tape k → Protocol R)
    (hk : k ≤ T) (hnext : ∀ bits, Fits (next bits) (T - k)) :
    (failingTapes (.query bad next) T ⟨hk, hnext⟩).card =
      ∑ bits : Tape k,
        if bits ∈ bad then 2 ^ (T - k)
        else (failingTapes (next bits) (T - k) (hnext bits)).card := by
  classical
  simp only [failingTapes]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro bits hb
    have hinj : Function.Injective
        (fun suffix : Tape (T - k) => (splitEquiv hk).symm (bits, suffix)) := by
      intro s₁ s₂ heq
      have hpair := (splitEquiv hk).symm.injective heq
      exact congrArg Prod.snd hpair
    rw [Finset.card_image_of_injective _ hinj]
    by_cases hmem : bits ∈ bad
    · simp [hmem]
    · simp [hmem]
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro tape htb htc
    rcases Finset.mem_image.mp htb with ⟨sufb, _, heqb⟩
    rcases Finset.mem_image.mp htc with ⟨sufc, _, heqc⟩
    have hpair := congrArg (splitEquiv hk) (heqb.trans heqc.symm)
    have hfirst : b = c := by simpa using congrArg Prod.fst hpair
    exact hne hfirst

/-- Under a sufficiently long fixed tape, the proportion of tapes which
fail is exactly the recursively defined adaptive failure mass. -/
lemma failingTapes_fraction_eq_failureMass {R : ℕ} (p : Protocol R)
    (T : ℕ) (hfit : Fits p T) :
    ((failingTapes p T hfit).card : ℚ) / (2 : ℚ) ^ T = failureMass p := by
  induction p generalizing T with
  | stop r =>
      simp [failingTapes, failureMass]
  | @query r k bad next ih =>
      rcases hfit with ⟨hk, hnext⟩
      let m : ℕ := T - k
      let s : ℚ := (2 : ℚ) ^ m
      have hspos : 0 < s := by positivity
      have hchild : ∀ bits : Tape k,
          ((failingTapes (next bits) m (hnext bits)).card : ℚ) =
            failureMass (next bits) * s := by
        intro bits
        have hfrac := ih bits m (hnext bits)
        field_simp [s] at hfrac ⊢
        simpa [s, m, mul_comm] using hfrac
      have hsum :
          (∑ bits : Tape k,
            if bits ∈ bad then s
            else (failingTapes (next bits) m (hnext bits)).card) =
          s * ((bad.card : ℚ) +
            ∑ bits : Tape k,
              if bits ∈ bad then 0 else failureMass (next bits)) := by
        calc
          (∑ bits : Tape k,
            if bits ∈ bad then s
            else (failingTapes (next bits) m (hnext bits)).card) =
              ∑ bits : Tape k,
                s * (if bits ∈ bad then 1 else failureMass (next bits)) := by
                  apply Finset.sum_congr rfl
                  intro bits _
                  by_cases hmem : bits ∈ bad
                  · simp [hmem]
                  · simp [hmem, hchild bits, mul_comm]
          _ = s * ((bad.card : ℚ) +
                ∑ bits : Tape k,
                  if bits ∈ bad then 0 else failureMass (next bits)) := by
                  rw [← Finset.mul_sum]
                  congr 1
                  have hsplit (bits : Tape k) :
                      (if bits ∈ bad then (1 : ℚ) else failureMass (next bits)) =
                        (if bits ∈ bad then (1 : ℚ) else 0) +
                          (if bits ∈ bad then 0 else failureMass (next bits)) := by
                    by_cases hmem : bits ∈ bad <;> simp [hmem]
                  calc
                    (∑ bits : Tape k,
                        if bits ∈ bad then (1 : ℚ) else failureMass (next bits)) =
                        ∑ bits : Tape k,
                          ((if bits ∈ bad then (1 : ℚ) else 0) +
                            (if bits ∈ bad then 0 else failureMass (next bits))) := by
                              apply Finset.sum_congr rfl
                              intro bits _
                              exact hsplit bits
                    _ = (∑ bits : Tape k, if bits ∈ bad then (1 : ℚ) else 0) +
                        ∑ bits : Tape k, if bits ∈ bad then 0 else failureMass (next bits) :=
                          Finset.sum_add_distrib
                    _ = (bad.card : ℚ) +
                        ∑ bits : Tape k, if bits ∈ bad then 0 else failureMass (next bits) := by
                          simp
      have hnat := card_failingTapes_query (R := r) (T := T)
        (bad := bad) (next := next) hk hnext
      have hcard :
          ((failingTapes (.query bad next) T ⟨hk, hnext⟩).card : ℚ) =
            s * ((bad.card : ℚ) +
              ∑ bits : Tape k,
                if bits ∈ bad then 0 else failureMass (next bits)) := by
        rw [hnat]
        simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_pow]
        simpa [s, m] using hsum
      have hpow : (2 : ℚ) ^ T = (2 : ℚ) ^ k * s := by
        rw [← Nat.add_sub_of_le hk]
        simp [pow_add, s, m]
      rw [hcard, failureMass, hpow]
      field_simp

/-- If each reachable query has bad fraction at most `ε`, then at most
`R * ε * 2^T` of the fixed length-`T` tapes fail, provided every execution
path consumes at most `T` bits. -/
lemma failingTapes_card_le {R : ℕ} (p : Protocol R) (ε : ℚ)
    (hε : 0 ≤ ε) (hvalid : LocallyBounded ε p) (T : ℕ)
    (hT : maxConsumedBits p ≤ T) :
    ((failingTapes p T (fits_of_maxConsumedBits p T hT)).card : ℚ) ≤
      (R : ℚ) * ε * (2 : ℚ) ^ T := by
  have hfrac := failingTapes_fraction_eq_failureMass p T
    (fits_of_maxConsumedBits p T hT)
  have hmass := failureMass_le p ε hε hvalid
  have hpow : (2 : ℚ) ^ T ≠ 0 := by positivity
  have hcard :
      ((failingTapes p T (fits_of_maxConsumedBits p T hT)).card : ℚ) =
        failureMass p * (2 : ℚ) ^ T := by
    field_simp [hpow] at hfrac ⊢
    exact hfrac
  calc
    ((failingTapes p T (fits_of_maxConsumedBits p T hT)).card : ℚ) =
        failureMass p * (2 : ℚ) ^ T := hcard
    _ ≤ ((R : ℚ) * ε) * (2 : ℚ) ^ T :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = (R : ℚ) * ε * (2 : ℚ) ^ T := by ring

end Lax235315Proofs.Construction.AdaptiveTapeCounting
