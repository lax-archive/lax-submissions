import Lax185574Proofs.ResolveRam.SizeGlue.State
import Lax185574Proofs.ResolveRam.SizeGlue.Calls

/-!
The sizes that bound the cost of a round of the glue program.

Write `M` for the largest size of a tree of the family, `T` for
`treeCount` and `Y = M + T + 1`. `SzKit C A` collects the bounds on the
words that a round of the glue program reads or writes: the state, the
answers and queries of the calls, the number of items of a level are at
most `C (n + 1) Y^A`, and the item trees, the answers of the rank shift,
of the far tree and of the compositions, and the output words of the
items are at most `C Y^A`. Such `C` and `A` exist (`szKit`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.TreeAlgo
open Lax185574Proofs.ResolveRam Lax185574Proofs.Words Lax185574Proofs.TypeTreeSizes
open Lax185574Proofs.MC Lax3.DistFO

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The quantity `Y = M + T + 1`. -/
noncomputable def yQ : ℕ := maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1

/-- The bounds on the words of a round. -/
structure SzKit (C A : ℕ) : Prop where
  st : ∀ c : Cur, (c = .stp ∨ c = .fin ∨ Valid G P Q s k₀ q₀ c) →
    (stOf G P Q s k₀ q₀ c).length ≤ C * (n + 1) * yQ G P Q s k₀ q₀ ^ A
  call : ∀ c ∈ rcalls G P Q s k₀ q₀, c ≠ .stp →
    (realQ G k₀ q₀ c).length + (rQ G k₀ q₀ c).length + (rY G k₀ q₀ c).length ≤
      C * (n + 1) * yQ G P Q s k₀ q₀ ^ A
  stpY : (rY G k₀ q₀ .stp).length ≤ C * (n + 1) * yQ G P Q s k₀ q₀ ^ A
  item : ∀ d ≤ q₀, ∀ x ∈ lvR G P Q s k₀ q₀ d, wordLength x.2 ≤ C * yQ G P Q s k₀ q₀ ^ A
  shift : ∀ d < q₀, ∀ x ∈ lvR G P Q s k₀ q₀ d, wordLength (shOf G x.2) ≤ C * yQ G P Q s k₀ q₀ ^ A
  fa : ∀ d < q₀, ∀ x ∈ lvR G P Q s k₀ q₀ d, ∀ ν ∈ faOf G x.2, wordLength ν ≤ C * yQ G P Q s k₀ q₀ ^ A
  co : ∀ d < q₀, ∀ x ∈ lvR G P Q s k₀ q₀ d, ∀ ν ∈ faOf G x.2,
    wordLength (coOf G (shOf G x.2) ν) ≤ C * yQ G P Q s k₀ q₀ ^ A
  lv : ∀ d ≤ q₀, (lvR G P Q s k₀ q₀ d).length ≤ C * (n + 1) * yQ G P Q s k₀ q₀ ^ A
  out : ∀ d ≤ q₀, ∀ w ∈ outW G P Q s k₀ q₀ d, w.length ≤ C * yQ G P Q s k₀ q₀ ^ A
  T : treeCount G (resolveBy G s P Q) k₀ q₀ ≤ C * yQ G P Q s k₀ q₀ ^ A

theorem one_le_yQ : 1 ≤ yQ G P Q s k₀ q₀ := by unfold yQ; omega

theorem M_pow_le (a : ℕ) : (maxTreeSize G k₀ q₀ + 1) ^ a ≤ yQ G P Q s k₀ q₀ ^ a :=
  Nat.pow_le_pow_left (by unfold yQ; omega) a

theorem kidB_le : kidB k₀ q₀ (treeCount G (resolveBy G s P Q) k₀ q₀) ≤
    (kidB k₀ q₀ 0 + 3) * yQ G P Q s k₀ q₀ ^ (q₀ + 1) := by
  unfold kidB
  set S := ∑ m ∈ Finset.range (q₀ + 1), sizeCoeff (1 + 36 * (rhoPlus k₀ q₀ + 1) * ((q₀ + 1) * (q₀ + 1)))
    (q₀ + 1) m
  have h1 : (treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ (q₀ + 1) ≤ yQ G P Q s k₀ q₀ ^ (q₀ + 1) :=
    Nat.pow_le_pow_left (by unfold yQ; omega) _
  have h2 : 1 ≤ yQ G P Q s k₀ q₀ ^ (q₀ + 1) := Nat.one_le_pow _ _ (one_le_yQ G P Q s k₀ q₀)
  simp only [zero_add, one_pow, mul_one]
  nlinarith

/-- A bound `c Y^a` is also a bound `C Y^A` for larger `C` and `A`. -/
theorem le_up {Y c a C A x : ℕ} (hY : 1 ≤ Y) (h : x ≤ c * Y ^ a) (hc : c ≤ C) (ha : a ≤ A) : x ≤ C * Y ^ A :=
  le_trans h (Nat.mul_le_mul hc (Nat.pow_le_pow_right hY ha))

theorem le_up' {Y c a C A x N : ℕ} (hY : 1 ≤ Y) (h : x ≤ c * (N + 1) * Y ^ a) (hc : c ≤ C) (ha : a ≤ A) :
    x ≤ C * (N + 1) * Y ^ A :=
  le_trans h (Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) (Nat.pow_le_pow_right hY ha))

/-- **The bounds on the words of a round exist.** -/
theorem szKit (hk : 1 ≤ k₀) : ∃ C A : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool),
    SzKit G P Q s k₀ q₀ C A := by
  obtain ⟨c1, a1, h1⟩ := stOf_len k₀ q₀ hk
  obtain ⟨c2, a2, h2⟩ := rcall_le_nY (k₀ := k₀) (q₀ := q₀) hk
  obtain ⟨c3, a3, h3⟩ := stp_ans_le (k₀ := k₀) (q₀ := q₀) hk
  obtain ⟨c4, a4, h4⟩ := item_le_all k₀ q₀ hk
  obtain ⟨c5, a5, h5⟩ := shift_ans_le (q₀ := q₀) hk
  obtain ⟨c6, a6, h6⟩ := faOf_mem_le (q₀ := q₀) hk
  obtain ⟨c7, a7, h7⟩ := compose_ans_le (q₀ := q₀) hk
  set c8 := ((k₀ + q₀ + 2) ^ 2 + 1) ^ q₀
  set c9 := kidB k₀ q₀ 0 + 3
  refine ⟨c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + 1, a1 + a2 + a3 + a4 + a5 + a6 + a7 + q₀ + 1,
    fun n G P Q s => ?_⟩
  have hY := one_le_yQ G P Q s k₀ q₀
  have hYd : maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1 = yQ G P Q s k₀ q₀ := rfl
  refine ⟨fun c hc => ?_, fun c hc hne => ?_, ?_, fun d hd x hx => ?_, fun d hd x hx => ?_,
    fun d hd x hx ν hν => ?_, fun d hd x hx ν hν => ?_, fun d hd => ?_, fun d hd w hw => ?_, ?_⟩
  · have := h1 n G P Q s c hc; rw [hYd] at this
    exact le_up' hY this (by omega) (by omega)
  · have := h2 n G P Q s c hc hne; rw [hYd] at this
    exact le_up' hY (by omega) (show c2 ≤ _ by omega) (show a2 ≤ _ by omega)
  · have := h3 n G
    have e := M_pow_le G P Q s k₀ q₀ a3
    refine le_up' hY (c := c3) (a := a3) (le_trans (by omega) (Nat.mul_le_mul_left _ e)) (by omega) (by omega)
  · have := h4 d hd n G P Q s x hx
    exact le_up hY (le_trans this (Nat.mul_le_mul_left _ (M_pow_le G P Q s k₀ q₀ a4))) (by omega) (by omega)
  · have := h5 d hd n G P Q s x hx
    exact le_up hY (c := c5) (a := a5) (le_trans (by omega) (Nat.mul_le_mul_left c5 (M_pow_le G P Q s k₀ q₀ a5))) (by omega)
      (by omega)
  · have := h6 d hd n G P Q s x hx ν hν
    exact le_up hY (le_trans this (Nat.mul_le_mul_left _ (M_pow_le G P Q s k₀ q₀ a6))) (by omega) (by omega)
  · have := h7 d hd n G P Q s x hx ν hν
    exact le_up hY (c := c7) (a := a7) (le_trans (by omega) (Nat.mul_le_mul_left c7 (M_pow_le G P Q s k₀ q₀ a7))) (by omega)
      (by omega)
  · have := lvR_len G P Q s k₀ q₀ hk hd; rw [hYd] at this
    exact le_up' hY this (by omega) (by omega)
  · have := outW_mem_le G P Q s k₀ q₀ hk hd w hw
    exact le_up hY (le_trans this (kidB_le G P Q s k₀ q₀)) (by omega) (by omega)
  · have : treeCount G (resolveBy G s P Q) k₀ q₀ ≤ 1 * yQ G P Q s k₀ q₀ ^ 1 := by
      simp only [pow_one, one_mul]; unfold yQ; omega
    exact le_up hY this (by omega) (by omega)

end Lax185574Proofs.ResolveRam.Glue
