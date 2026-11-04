import Lax185574Proofs.Chain.Ram.ChainSeq
import Lax185574Proofs.Chain.Main

/-!
The running time of the chain program on the members of a monadically
dependent class.

The damping loop runs one round per set of the damping sequence, so at
most `2r/ε + 1` rounds. A round tries the values `κ = 1, 2, …` and stops
at the first accepted one, which is at most
`K = max γ_r (max (min n (4 γ₁ (log₂ n + 1))) 1)` by the predamping bound.
Each try costs `O((r+1)(n+1)^3)`. As `K` is subpolynomial on the class,
the total cost is at most `c (n+1)^{3+δ}` for every `δ > 0`
(`chain_cost_bound`).

The Welzl ordering is computed by a program whose cost is governed by
the largest number `K_w` of steps crossed by one vertex. It satisfies
`K_w < (s+1)(log₂ n + 1)` with `s = 4 γ₁ (log₂ n + 1)`, so it is
subpolynomial as well (`welzl_cost_bound`).
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax185574Proofs.Chain
open Lax199508.GraphClasses Lax710763.MonadicDependence

/-! ### Polynomial times subpolynomial -/

/-- A subpolynomial factor raises the exponent `k` by an arbitrary `δ > 0`. -/
theorem _root_.Lax185574Proofs.Chain.SubpolyOn.pow_mul_le {C : GraphClass} {f : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ}
    (hf : SubpolyOn C f) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ((n : ℝ) + 1) ^ k * f n G ≤ c * ((n : ℝ) + 1) ^ ((k : ℝ) + δ) := by
  obtain ⟨c, hc⟩ := hf δ hδ
  refine ⟨c, fun n G hG => ?_⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc ((n : ℝ) + 1) ^ k * f n G ≤ ((n : ℝ) + 1) ^ k * (c * ((n : ℝ) + 1) ^ δ) :=
        mul_le_mul_of_nonneg_left (hc n G hG) (by positivity)
    _ = c * (((n : ℝ) + 1) ^ (k : ℝ) * ((n : ℝ) + 1) ^ δ) := by rw [Real.rpow_natCast]; ring
    _ = c * ((n : ℝ) + 1) ^ ((k : ℝ) + δ) := by rw [← Real.rpow_add hn]

/-- **Cubic times subpolynomial.** -/
theorem _root_.Lax185574Proofs.Chain.SubpolyOn.cube_mul_le {C : GraphClass} {f : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ}
    (hf : SubpolyOn C f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ((n : ℝ) + 1) ^ 3 * f n G ≤ c * ((n : ℝ) + 1) ^ (3 + δ) := by
  obtain ⟨c, hc⟩ := hf.pow_mul_le 3 hδ
  refine ⟨c, fun n G hG => ?_⟩
  have := hc n G hG
  push_cast at this
  exact this

/-! ### The number of tries of one damping step -/

section Tries

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- The damping step stops at the first accepted `κ`. -/
theorem dampTries_le_of {r : ℕ} {o : VOrder (Fin n)} {q : ℕ} {A : Finset (Fin n)} {κ : ℕ}
    (hκ1 : 1 ≤ κ) (hκn : κ ≤ n) (hp : accK G r o q A κ = true) :
    dampTries G r o q A ≤ κ := by
  unfold dampTries
  obtain ⟨a, ha⟩ := firstFrom_isSome (p := accK G r o q A) (k := 1) (f := n) (b := κ) hκ1
    (by omega) hp
  rw [ha]
  dsimp only
  obtain ⟨-, -, hmin⟩ := firstFrom_some ha
  by_contra h
  have := hmin κ hκ1 (by omega)
  rw [hp] at this
  exact absurd this (by simp)

/-- **The number of tries.** For `|A| ≥ 6(q+1)` the damping step accepts
some `κ ≤ max γ_r (max (min n (4 γ₁ (log₂ n + 1))) 1)`. -/
theorem dampTries_le_max (r : ℕ) (o : VOrder (Fin n)) (q : ℕ) {A : Finset (Fin n)}
    (hA : 6 * (q + 1) ≤ A.card) :
    dampTries G r o q A ≤ max (growth (fun B => tpRel G B r))
      (max (min n (4 * growth (fun B => tpRel G B 0) * (Nat.log 2 n + 1))) 1) := by
  set K := max (growth (fun B => tpRel G B r))
      (max (min n (4 * growth (fun B => tpRel G B 0) * (Nat.log 2 n + 1))) 1)
  have hn1 : 1 ≤ n := by
    have := card_le_univ A
    simp only [Fintype.card_fin] at this
    omega
  have hK1 : 1 ≤ K := le_max_of_le_right (le_max_right _ _)
  have hKn : K ≤ n := by
    have hγ := growth_le_card (fun B => tpRel G B r)
    rw [Fintype.card_fin] at hγ
    exact max_le hγ (max_le (min_le_left _ _) hn1)
  have hβ := isPackingBound_min (G := G)
  rw [Fintype.card_fin] at hβ
  have hp : q * (predamp G (fun B => tpRel G B r) o A q K).card ≤ A.card :=
    predamp_card (isSelector_tp (G := G) r) hK1
      (fun B hB => (numCls_le_growth_mul (fun B => tpRel G B r) hB).trans
        (Nat.mul_le_mul_right _ (le_max_left _ _)))
      (hβ.mono (le_max_of_le_right (le_max_left _ _))) hA
  exact dampTries_le_of hK1 hKn (by unfold accK; simpa using hp)

/-- The cost of one predamping try is cubic. -/
theorem kapCost_le (n r : ℕ) : kapCost n r + 30 ≤ 6000 * ((r + 1) * (n + 1) ^ 3) := by
  unfold kapCost appCost prepCost r23Cost tpCost
  ring_nf
  nlinarith [Nat.zero_le (r * n ^ 3), Nat.zero_le (r * n ^ 2), Nat.zero_le (r * n),
    Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 2), Nat.zero_le n, Nat.zero_le r]

/-- **The cost of one damping step.** -/
theorem dampCost_le (r : ℕ) (o : VOrder (Fin n)) (q : ℕ) (A : Finset (Fin n)) :
    dampCost G r o q A ≤ max (growth (fun B => tpRel G B r))
      (max (min n (4 * growth (fun B => tpRel G B 0) * (Nat.log 2 n + 1))) 1) *
        (kapCost n r + 30) + n * 30 + 100 := by
  unfold dampCost
  split_ifs with h
  · omega
  · have := Nat.mul_le_mul_right (kapCost n r + 30) (dampTries_le_max (G := G) r o q
      (A := A) (by omega))
    omega

/-- **The cost of one round of the loop**, with `K` as in `dampTries_le_max`. -/
theorem sCost_le (r : ℕ) (o : VOrder (Fin n)) (q j : ℕ) :
    sCost G r o q j ≤ 6000 * (max (growth (fun B => tpRel G B r))
      (max (min n (4 * growth (fun B => tpRel G B 0) * (Nat.log 2 n + 1))) 1) + 1) *
        ((r + 1) * (n + 1) ^ 3) := by
  set K := max (growth (fun B => tpRel G B r))
      (max (min n (4 * growth (fun B => tpRel G B 0) * (Nat.log 2 n + 1))) 1)
  set P := (r + 1) * (n + 1) ^ 3
  have hd : dampCost G r o q (dIter G r o q j) ≤ K * (kapCost n r + 30) + n * 30 + 100 :=
    dampCost_le (G := G) r o q (dIter G r o q j)
  have hk : K * (kapCost n r + 30) ≤ K * (6000 * P) := Nat.mul_le_mul_left K (kapCost_le n r)
  have hP : n + 1 ≤ P := by
    have h1 : n + 1 ≤ (n + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h2 : (n + 1) ^ 3 ≤ P := Nat.le_mul_of_pos_left _ (by omega)
    omega
  unfold sCost
  have : 6000 * (K + 1) * P = K * (6000 * P) + 6000 * P := by ring
  rw [this]
  omega

end Tries

/-! ### The number of rounds -/

section Rounds

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- The chain has one set more than the damping sequence. -/
theorem dLen_add_one {r : ℕ} {ε : ℚ} (hn : 2 ≤ n) (hε : 0 < ε) :
    dLen G r (welzlVOrder G) (qOf n r ε) + 1 = (chainAlg G r ε).length := by
  obtain ⟨hq2, -⟩ := qOf_spec (r := r) hn hε
  unfold chainAlg
  rw [if_neg (by rw [Fintype.card_fin]; omega), length_suffixUnions]
  unfold chainSeq
  simp only [Fintype.card_fin]
  rw [List.length_append, dampSeq_eq _ _ hq2]
  simp

/-- The damping sequence has at most `2r/ε + 1` sets. -/
theorem dLen_le_real {r : ℕ} {ε : ℚ} (hn : 2 ≤ n) (hε : 0 < ε) :
    (dLen G r (welzlVOrder G) (qOf n r ε) : ℝ) ≤ 2 * r / (ε : ℝ) + 1 := by
  have h := chainAlg_length (G := G) (r := r) hε
  rw [← dLen_add_one hn hε] at h
  have : (((dLen G r (welzlVOrder G) (qOf n r ε) + 1 : ℕ) : ℚ) : ℝ) ≤
      ((2 * r / ε + 2 : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at this
  linarith

end Rounds

/-! ### Steps of the Welzl procedure crossed by a vertex -/

section Welzl

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Crossed steps.** If the atomic types of `G` grow with ratio `γ`,
every vertex crosses fewer than `(s+1)(log₂ n + 1)` steps of the Welzl
procedure, where `s = 4γ(log₂ n + 1)`. -/
theorem stepCross_welzlTree_lt {γ : ℕ}
    (hγ : ∀ Y : Finset V, Y.Nonempty → numCls (tpRel G Y 0) univ ≤ γ * Y.card) (x : V) :
    stepCross G x (welzlTree G).steps <
      (4 * γ * (Nat.log 2 (Fintype.card V) + 1) + 1) * (Nat.log 2 (Fintype.card V) + 1) := by
  set n := Fintype.card V
  set s := 4 * γ * (Nat.log 2 n + 1)
  have hn : 1 ≤ n := Fintype.card_pos_iff.2 ⟨x⟩
  have hpot := potential_run (G := G) hγ n (st := ⟨univ, fun _ => 1, []⟩) (fun _ => le_rfl)
  simp only [card_univ, sum_const, smul_eq_mul, mul_one] at hpot
  change (∑ y, (welzlTree G).w y) * (welzlTree G).active.card ^ s ≤ n * n ^ s at hpot
  have hact : 1 ≤ (welzlTree G).active.card := by
    rcases Nat.eq_zero_or_pos (welzlTree G).active.card with h | h
    · exfalso
      rw [card_eq_zero] at h
      have hcov := (welzlTree_inv (G := G)).cover
      have hv := (welzlTree_inv (G := G)).valid
      have hfold := fold_spec (G := G) (welzlTree G).steps (welzlTree G).active
        ((welzlTree G).active.sort (· ≤ ·)) hv (sort_nodup _ _) (fun x => mem_sort _)
      revert hv hcov hfold
      rw [h]
      intro hcov hv _
      cases hs : (welzlTree G).steps with
      | nil => have := hcov x; rw [hs] at this; simp at this
      | cons p rest => rw [hs] at hv; exact absurd hv.2.1 (notMem_empty _)
    · exact h
  have hW : (∑ y, (welzlTree G).w y) ≤ n * n ^ s :=
    (Nat.le_mul_of_pos_right _ (pow_pos hact s)).trans hpot
  have hwx : 2 ^ stepCross G x (welzlTree G).steps ≤ n ^ (s + 1) := by
    rw [← (welzlTree_inv (G := G)).weight x, pow_succ, Nat.mul_comm]
    exact (single_le_sum (f := (welzlTree G).w) (fun _ _ => Nat.zero_le _) (mem_univ x)).trans hW
  have hlog : n ^ (s + 1) < 2 ^ ((s + 1) * (Nat.log 2 n + 1)) := by
    rw [pow_mul']
    exact Nat.pow_lt_pow_left (Nat.lt_pow_succ_log_self (by norm_num) n) (by omega)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (lt_of_le_of_lt hwx hlog)

/-- The largest number of crossed steps. -/
theorem sup_stepCross_welzlTree_lt {γ : ℕ}
    (hγ : ∀ Y : Finset V, Y.Nonempty → numCls (tpRel G Y 0) univ ≤ γ * Y.card) :
    (univ.sup fun x => stepCross G x (welzlTree G).steps) + 1 ≤
      (4 * γ * (Nat.log 2 (Fintype.card V) + 1) + 1) * (Nat.log 2 (Fintype.card V) + 1) := by
  have h0 : 1 ≤ (4 * γ * (Nat.log 2 (Fintype.card V) + 1) + 1) *
      (Nat.log 2 (Fintype.card V) + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have := Finset.sup_le (s := univ) (f := fun x => stepCross G x (welzlTree G).steps)
    (a := (4 * γ * (Nat.log 2 (Fintype.card V) + 1) + 1) * (Nat.log 2 (Fintype.card V) + 1) - 1)
    (fun x _ => by have := stepCross_welzlTree_lt G hγ x; omega)
  omega

end Welzl

/-! ### The bounds on a class -/

/-- **Running time of the chain program.** On a monadically dependent
class, for `r ≥ 1`, rational `ε > 0` and real `δ > 0`, the cost of the
damping loop is at most `c (n+1)^{3+δ}` for all `n ≥ 2`. -/
theorem chain_cost_bound (C : GraphClass) (hC : MonadicallyDependent C) (r : ℕ) (ε : ℚ)
    (hr : 1 ≤ r) (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], 2 ≤ n → C n G →
      ((∑ j ∈ range (dLen G r (welzlVOrder G) (qOf n r ε)),
          sCost G r (welzlVOrder G) (qOf n r ε) j : ℕ) : ℝ) ≤
        c * ((n : ℝ) + 1) ^ (3 + δ) := by
  have hγ1 := subpolyOn_growth C hC 0
  have hγr := subpolyOn_growth C hC r
  have hL := subpolyOn_log (C := C)
  let γ1f : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n G =>
    (@growth (Fin n) _ _ (fun B => @tpRel (Fin n) _ _ G (Classical.decRel _) B 0) : ℝ)
  let γrf : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n G =>
    (@growth (Fin n) _ _ (fun B => @tpRel (Fin n) _ _ G (Classical.decRel _) B r) : ℝ)
  let Lf : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n _ => ((Nat.log 2 n : ℕ) : ℝ) + 1
  have h0γ1 : ∀ n G, C n G → 0 ≤ γ1f n G := fun _ _ _ => Nat.cast_nonneg _
  have h0L : ∀ n G, C n G → 0 ≤ Lf n G := fun _ _ _ => by positivity
  let Kf : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n G => γrf n G + 4 * γ1f n G * Lf n G + 2
  have hKf : SubpolyOn C Kf := by
    have hγ1L : SubpolyOn C (fun n G => γ1f n G * Lf n G) := hγ1.mul hL h0γ1 h0L
    refine SubpolyOn.add (SubpolyOn.add hγr ?_) (SubpolyOn.const 2)
    have := (SubpolyOn.const (C := C) 4).mul hγ1L (fun _ _ _ => by norm_num)
      (fun n G hG => mul_nonneg (h0γ1 n G hG) (h0L n G hG))
    refine this.mono fun n G _ => le_of_eq ?_
    ring
  obtain ⟨c', hc'⟩ := hKf.cube_mul_le hδ
  set D : ℝ := (2 * r / (ε : ℝ) + 1) * 6000 * (r + 1)
  have hD : 0 ≤ D := by
    have : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε.le
    positivity
  refine ⟨D * c', fun n G inst hn hG => ?_⟩
  have eγ1 : γ1f n G = (growth (fun B => tpRel G B 0) : ℝ) := by
    obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
    rfl
  have eγr : γrf n G = (growth (fun B => tpRel G B r) : ℝ) := by
    obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
    rfl
  set o := welzlVOrder G
  set q := qOf n r ε
  set γ1 := growth (fun B => tpRel G B 0)
  set γr := growth (fun B => tpRel G B r)
  set K := max γr (max (min n (4 * γ1 * (Nat.log 2 n + 1))) 1)
  set M := dLen G r o q
  -- the sum in `ℕ`
  have hsum : ∑ j ∈ range M, sCost G r o q j ≤ M * (6000 * (K + 1) * ((r + 1) * (n + 1) ^ 3)) := by
    have := Finset.sum_le_card_nsmul (range M) (sCost G r o q)
      (6000 * (K + 1) * ((r + 1) * (n + 1) ^ 3)) (fun j _ => sCost_le (G := G) r o q j)
    simpa using this
  have hsumR : ((∑ j ∈ range M, sCost G r o q j : ℕ) : ℝ) ≤
      (M : ℝ) * (6000 * ((K : ℝ) + 1) * ((r + 1) * ((n : ℝ) + 1) ^ 3)) := by
    exact_mod_cast hsum
  -- `K + 1 ≤ Kf`
  have hKle : (K : ℝ) + 1 ≤ Kf n G := by
    have : K ≤ γr + 4 * γ1 * (Nat.log 2 n + 1) + 1 := by
      simp only [K]
      refine max_le (by omega) (max_le ((min_le_right _ _).trans (by omega)) (by omega))
    have : (K : ℝ) ≤ γr + 4 * γ1 * ((Nat.log 2 n : ℕ) + 1) + 1 := by exact_mod_cast this
    simp only [Kf, Lf]
    rw [eγ1, eγr]
    linarith
  have hM := dLen_le_real (G := G) (r := r) hn hε
  have hMe : (0 : ℝ) ≤ 2 * r / (ε : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε.le
    positivity
  have hcube := hc' n G hG
  calc ((∑ j ∈ range M, sCost G r o q j : ℕ) : ℝ)
      ≤ (M : ℝ) * (6000 * ((K : ℝ) + 1) * ((r + 1) * ((n : ℝ) + 1) ^ 3)) := hsumR
    _ ≤ (2 * r / (ε : ℝ) + 1) * (6000 * Kf n G * ((r + 1) * ((n : ℝ) + 1) ^ 3)) := by
        gcongr
    _ = D * (((n : ℝ) + 1) ^ 3 * Kf n G) := by simp only [D]; ring
    _ ≤ D * (c' * ((n : ℝ) + 1) ^ (3 + δ)) := mul_le_mul_of_nonneg_left hcube hD
    _ = D * c' * ((n : ℝ) + 1) ^ (3 + δ) := by ring

/-- **Running time of the Welzl program.** On a monadically dependent
class, for real `δ > 0`, with `K_w` the largest number of steps of the
Welzl procedure crossed by one vertex,
`(n+1)^3 (K_w + 1)(K_w + log₂ n + 2) ≤ c (n+1)^{3+δ}`. -/
theorem welzl_cost_bound (C : GraphClass) (hC : MonadicallyDependent C) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], C n G →
      ((n : ℝ) + 1) ^ 3 *
          (((univ.sup fun x => stepCross G x (welzlTree G).steps : ℕ) : ℝ) + 1) *
          (((univ.sup fun x => stepCross G x (welzlTree G).steps : ℕ) : ℝ) +
            (Nat.log 2 n : ℝ) + 2) ≤
        c * ((n : ℝ) + 1) ^ (3 + δ) := by
  have hγ1 := subpolyOn_growth C hC 0
  have hL := subpolyOn_log (C := C)
  let γ1f : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n G =>
    (@growth (Fin n) _ _ (fun B => @tpRel (Fin n) _ _ G (Classical.decRel _) B 0) : ℝ)
  let Lf : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n _ => ((Nat.log 2 n : ℕ) : ℝ) + 1
  have h0γ1 : ∀ n G, C n G → 0 ≤ γ1f n G := fun _ _ _ => Nat.cast_nonneg _
  have h0L : ∀ n G, C n G → 0 ≤ Lf n G := fun _ _ _ => by positivity
  have hγ1L : SubpolyOn C (fun n G => γ1f n G * Lf n G) := hγ1.mul hL h0γ1 h0L
  have h4 : SubpolyOn C (fun n G => 4 * (γ1f n G * Lf n G)) :=
    (SubpolyOn.const (C := C) 4).mul hγ1L (fun _ _ _ => by norm_num)
      (fun n G hG => mul_nonneg (h0γ1 n G hG) (h0L n G hG))
  let af : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n G => (4 * (γ1f n G * Lf n G) + 1) * Lf n G
  let bf : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n G => (4 * (γ1f n G * Lf n G) + 2) * Lf n G
  have h0a : ∀ n G, C n G → 0 ≤ af n G := fun n G hG => by
    have := h0γ1 n G hG; have := h0L n G hG; positivity
  have h0b : ∀ n G, C n G → 0 ≤ bf n G := fun n G hG => by
    have := h0γ1 n G hG; have := h0L n G hG; positivity
  have ha : SubpolyOn C af :=
    (h4.add (SubpolyOn.const 1)).mul hL (fun n G hG => by
      have := h0γ1 n G hG; have := h0L n G hG; positivity) h0L
  have hb : SubpolyOn C bf :=
    (h4.add (SubpolyOn.const 2)).mul hL (fun n G hG => by
      have := h0γ1 n G hG; have := h0L n G hG; positivity) h0L
  obtain ⟨c, hc⟩ := (ha.mul hb h0a h0b).cube_mul_le hδ
  refine ⟨c, fun n G inst hG => ?_⟩
  have eγ1 : γ1f n G = (growth (fun B => tpRel G B 0) : ℝ) := by
    obtain rfl : inst = Classical.decRel _ := Subsingleton.elim _ _
    rfl
  have hK := sup_stepCross_welzlTree_lt G (γ := growth (fun B => tpRel G B 0))
    (fun Y hY => numCls_le_growth_mul (fun B => tpRel G B 0) hY)
  rw [Fintype.card_fin] at hK
  have hcG := hc n G hG
  generalize (univ.sup fun x => stepCross G x (welzlTree G).steps) = Kw at hK ⊢
  generalize growth (fun B => tpRel G B 0) = γ1 at hK eγ1
  have hKR : ((Kw + 1 : ℕ) : ℝ) ≤ (((4 * γ1 * (Nat.log 2 n + 1) + 1) * (Nat.log 2 n + 1) : ℕ) : ℝ) :=
    Nat.cast_le.2 hK
  push_cast at hKR
  have hKa : (Kw : ℝ) + 1 ≤ af n G := by
    simp only [af, Lf]; rw [eγ1]; linarith
  have hKb : (Kw : ℝ) + (Nat.log 2 n : ℝ) + 2 ≤ bf n G := by
    simp only [bf, Lf]; rw [eγ1]; linarith
  have hpos : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := by positivity
  have h1 : (0 : ℝ) ≤ (Kw : ℝ) + (Nat.log 2 n : ℝ) + 2 := by positivity
  have h2 : (0 : ℝ) ≤ af n G := h0a n G hG
  calc ((n : ℝ) + 1) ^ 3 * ((Kw : ℝ) + 1) * ((Kw : ℝ) + (Nat.log 2 n : ℝ) + 2)
      ≤ ((n : ℝ) + 1) ^ 3 * af n G * bf n G :=
        mul_le_mul (mul_le_mul_of_nonneg_left hKa hpos) hKb h1 (mul_nonneg hpos h2)
    _ = ((n : ℝ) + 1) ^ 3 * (af n G * bf n G) := by ring
    _ ≤ c * ((n : ℝ) + 1) ^ (3 + δ) := hcG

end Lax185574Proofs.Chain.Ram
