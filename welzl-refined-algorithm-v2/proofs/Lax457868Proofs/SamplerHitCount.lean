import Mathlib.Tactic
import Lax457868Proofs.SamplerEpsilonNet

/-!
Exact first-moment and majority-counting bounds for finite uniform tapes.
All probabilities are represented by cardinality inequalities on the tape space.
-/

namespace Lax457868Proofs.SamplerHitCount

open Lax457868Proofs.SamplerUniformDraws
open Lax457868Proofs.SamplerEpsilonNet

variable {α : Type*} [DecidableEq α]

private lemma hitCount_cons {X D : Finset α} {n : ℕ}
    (a : {x // x ∈ X}) (tail : Tape X n) :
    hitCount D (Fin.cons a tail) =
      (if a.val ∈ D then 1 else 0) + hitCount D tail := by
  classical
  unfold hitCount
  rw [Finset.card_filter, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [← Finset.card_filter]

/-- Adding a first coordinate gives the exact recurrence for the total number
of hits over all tapes. -/
lemma sum_hitCount_succ {X D : Finset α} {n : ℕ} (hDX : D ⊆ X) :
    (∑ tape : Tape X (n + 1), hitCount D tape) =
      D.card * X.card ^ n + X.card * (∑ tape : Tape X n, hitCount D tape) := by
  classical
  let A := {a // a ∈ X}
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => A)
  have hsum := Fintype.sum_equiv e
    (fun p : A × Tape X n => hitCount D (Fin.cons p.1 p.2))
    (fun tape : Tape X (n + 1) => hitCount D tape)
    (by intro p; rfl)
  rw [← hsum, Fintype.sum_prod_type]
  simp_rw [hitCount_cons]
  have hhead : (∑ a : A, if a.val ∈ D then 1 else 0) = D.card := by
    rw [Finset.sum_boole]
    change (Finset.univ.filter (fun a : A => a.val ∈ D)).card = D.card
    rw [Finset.univ_eq_attach]
    have hfilter : X.filter (fun x => x ∈ D) = D := by
      ext x
      simp [hDX]
    change (X.attach.filter (fun a : X => a.val ∈ D)).card = D.card
    rw [Finset.filter_attach (p := fun x : α => x ∈ D) X]
    simp only [Finset.card_map, Finset.card_attach]
    rw [hfilter]
  have hconst (a : A) :
      (∑ tail : Tape X n, if a.val ∈ D then 1 else 0) =
        if a.val ∈ D then X.card ^ n else 0 := by
    by_cases ha : a.val ∈ D <;> simp [ha]
  calc
    (∑ a : A, ∑ tail : Tape X n,
        ((if a.val ∈ D then 1 else 0) + hitCount D tail)) =
        (∑ a : A, ∑ tail : Tape X n, (if a.val ∈ D then 1 else 0)) +
          (∑ a : A, ∑ tail : Tape X n, hitCount D tail) := by
            simp_rw [Finset.sum_add_distrib]
    _ = D.card * X.card ^ n + X.card * (∑ tail : Tape X n, hitCount D tail) := by
          have hfirst : (∑ a : A, if a.val ∈ D then X.card ^ n else 0) =
              D.card * X.card ^ n := by
            calc
              (∑ a ∈ (Finset.univ : Finset A), if a.val ∈ D then X.card ^ n else 0) =
                  X.card ^ n * (∑ a ∈ (Finset.univ : Finset A),
                    if a.val ∈ D then 1 else 0) := by
                    calc
                      (∑ a ∈ (Finset.univ : Finset A), if a.val ∈ D then X.card ^ n else 0) =
                          ∑ a ∈ (Finset.univ : Finset A),
                            X.card ^ n * (if a.val ∈ D then 1 else 0) := by
                              apply Finset.sum_congr rfl
                              intro a _
                              by_cases ha : a.val ∈ D <;> simp [ha]
                      _ = X.card ^ n * (∑ a ∈ (Finset.univ : Finset A),
                            if a.val ∈ D then 1 else 0) := by
                              rw [Finset.mul_sum]
              _ = D.card * X.card ^ n := by
                    have hh : (∑ a ∈ (Finset.univ : Finset A),
                        if a.val ∈ D then 1 else 0) = D.card := by simpa using hhead
                    rw [hh]
                    ring
          simp_rw [hconst]
          rw [hfirst]
          have htail : (∑ a : A, ∑ tail : Tape X n, hitCount D tail) =
              X.card * (∑ tail : Tape X n, hitCount D tail) := by
            rw [Finset.sum_const]
            simp [A]
          rw [htail]

/-- Cross-multiplied exact first moment: domain size times the total hit count
is `s * |D| * |X|^s`. This formulation also covers the empty tape. -/
lemma card_mul_sum_hitCount {X D : Finset α} {s : ℕ} (hDX : D ⊆ X) :
    X.card * (∑ tape : Tape X s, hitCount D tape) =
      s * D.card * X.card ^ s := by
  induction s with
  | zero => simp [hitCount]
  | succ n ih =>
      rw [sum_hitCount_succ hDX]
      rw [ih]
      ring

/-- Every tape has at most `s` hits. -/
lemma hitCount_le_length {X D : Finset α} {s : ℕ} (tape : Tape X s) :
    hitCount D tape ≤ s := by
  classical
  simpa [hitCount] using
    Finset.card_filter_le (Finset.univ : Finset (Fin s))
      (fun i => (tape i).val ∈ D)

/-- A strict majority range is hit on at least a third of all tapes at the
quarter-length threshold. The statement is cross-multiplied, with no
probability assumptions. -/
lemma majority_hit_tapes_lower_bound {X D : Finset α} {s q : ℕ}
    (hDX : D ⊆ X) (hX : X.Nonempty) (hmajority : X.card < 2 * D.card)
    (hs : 0 < s) (hq : 4 * q ≤ s) :
    3 * (Finset.univ.filter fun tape : Tape X s => q ≤ hitCount D tape).card ≥
      X.card ^ s := by
  classical
  let good := Finset.univ.filter fun tape : Tape X s => q ≤ hitCount D tape
  let bad := Finset.univ.filter fun tape : Tape X s => ¬ q ≤ hitCount D tape
  let total := X.card ^ s
  let S := ∑ tape : Tape X s, hitCount D tape
  have htotal : (Finset.univ : Finset (Tape X s)).card = total := by
    simp [total]
  have hparts : bad.card + good.card = total := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Tape X s)))
      (p := fun tape : Tape X s => q ≤ hitCount D tape)
    simpa [bad, good, htotal, Nat.add_comm] using h
  have hsplit :
      (∑ tape ∈ bad, hitCount D tape) +
        (∑ tape ∈ good, hitCount D tape) = S := by
    have h := Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (Tape X s)))
      (p := fun tape : Tape X s => q ≤ hitCount D tape)
      (f := fun tape => hitCount D tape)
    simpa [bad, good, S, Nat.add_comm] using h
  have hbad : (∑ tape ∈ bad, hitCount D tape) ≤ q * bad.card := by
    calc
      (∑ tape ∈ bad, hitCount D tape) ≤ ∑ _tape ∈ bad, q := by
        apply Finset.sum_le_sum
        intro tape ht
        have hlt : hitCount D tape < q := by
          have hnot := (Finset.mem_filter.mp ht).2
          omega
        omega
      _ = q * bad.card := by simp [Nat.mul_comm]
  have hgood : (∑ tape ∈ good, hitCount D tape) ≤ s * good.card := by
    calc
      (∑ tape ∈ good, hitCount D tape) ≤ ∑ _tape ∈ good, s := by
        apply Finset.sum_le_sum
        intro tape _
        exact hitCount_le_length tape
      _ = s * good.card := by simp [Nat.mul_comm]
  have hsumUpper : S ≤ q * bad.card + s * good.card := by
    rw [← hsplit]
    exact Nat.add_le_add hbad hgood
  have hMpos : 0 < X.card := hX.card_pos
  have htotalPos : 0 < total := by
    simp [total, hMpos]
  have hmajorHit : s * total < 2 * S := by
    have hscale : X.card * (s * total) < (2 * D.card) * (s * total) :=
      Nat.mul_lt_mul_of_pos_right hmajority (Nat.mul_pos hs htotalPos)
    have hcross : X.card * S = s * D.card * total := by
      simpa [S, total] using card_mul_sum_hitCount hDX
    have hscale' : X.card * (s * total) < X.card * (2 * S) := by
      calc
        X.card * (s * total) < (2 * D.card) * (s * total) := hscale
        _ = X.card * (2 * S) := by nlinarith [hcross]
    exact (Nat.mul_lt_mul_left hMpos).mp (by simpa using hscale')
  have hineq : s * bad.card < 2 * q * bad.card + s * good.card := by
    rw [← hparts] at hmajorHit
    nlinarith [hsumUpper, hmajorHit]
  by_contra hgoal
  have hbadLarge : 2 * good.card < bad.card := by
    have : 3 * good.card < total := by
      simpa [good, total] using Nat.lt_of_not_ge hgoal
    rw [← hparts] at this
    omega
  have hqb : 4 * q * bad.card ≤ s * bad.card :=
    Nat.mul_le_mul_right bad.card hq
  have htwice : 2 * s * bad.card < 4 * q * bad.card + 2 * s * good.card := by
    nlinarith [hineq]
  have hsmall : s * bad.card < s * (2 * good.card) := by
    nlinarith [htwice, hqb]
  have hcancel : bad.card < 2 * good.card :=
    (Nat.mul_lt_mul_left hs).mp hsmall
  omega

/-- The standard quarter-length threshold is obtained by instantiating the
majority lower bound with `q = s / 4`. -/
lemma quarter_hit_tapes_lower_bound {X D : Finset α} {s : ℕ}
    (hDX : D ⊆ X) (hX : X.Nonempty) (hmajority : X.card < 2 * D.card)
    (hs : 0 < s) :
    3 * (Finset.univ.filter fun tape : Tape X s => s / 4 ≤ hitCount D tape).card ≥
      X.card ^ s := by
  apply majority_hit_tapes_lower_bound hDX hX hmajority hs
  simpa [Nat.mul_comm] using Nat.div_mul_le_self s 4

end Lax457868Proofs.SamplerHitCount
