import Mathlib.Data.List.OfFn
import Lax3Proofs.Refine.CoverActiveRadixMath
import Lax3Proofs.Refine.CoverActiveBlock

/-!
# Executable stable radix pass for one active-cover block

This file begins the RAM refinement of `CoverActiveRadixMath.radixPass`.
The first leaf is the zero-digit count: it reads exactly the current block
segment, leaves every array untouched, and returns the split point needed
by the stable scatter.  Its cost is linear in the block length and contains
no carrier scan.
-/

namespace Lax3Proofs.Refine.CoverActiveRadixPass

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Refine.CoverActiveRadixMath

/-! ## Array/list bridge -/

/-- The half-open array segment `[lo, lo + m)` as a list. -/
def segment (lo m : ℕ) (X : ℕ → ℕ) : List ℕ :=
  List.ofFn fun i : Fin m => X (lo + i)

@[simp] theorem segment_length (lo m : ℕ) (X : ℕ → ℕ) :
    (segment lo m X).length = m := by
  simp [segment]

@[simp] theorem segment_getElem (lo m : ℕ) (X : ℕ → ℕ) (i : ℕ)
    (hi : i < (segment lo m X).length) :
    (segment lo m X)[i] = X (lo + i) := by
  simp [segment]

theorem mem_segment_iff {lo m x : ℕ} {X : ℕ → ℕ} :
    x ∈ segment lo m X ↔ ∃ i < m, X (lo + i) = x := by
  simp only [segment, List.mem_ofFn]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, i.isLt, hi⟩
  · rintro ⟨i, hi, hxi⟩
    exact ⟨⟨i, hi⟩, hxi⟩

theorem pairwise_segment_iff {lo m : ℕ} {X : ℕ → ℕ} {R : ℕ → ℕ → Prop} :
    (segment lo m X).Pairwise R ↔
      ∀ i j, i < j → j < m → R (X (lo + i)) (X (lo + j)) := by
  rw [segment, List.pairwise_ofFn]
  constructor
  · intro h i j hij hj
    exact h (i := ⟨i, by omega⟩) (j := ⟨j, hj⟩) (by simpa using hij)
  · intro h i j hij
    exact h i j (by simpa using hij) j.isLt

/-- Number of zero digits seen in the first `k` entries. -/
def zeroCount (b : ℕ) (xs : List ℕ) (k : ℕ) : ℕ :=
  ((xs.take k).filter (digitZero b)).length

theorem zeroCount_le (b : ℕ) (xs : List ℕ) (k : ℕ) : zeroCount b xs k ≤ k := by
  exact le_trans (List.length_filter_le _ _) (List.length_take_le _ _)

@[simp] theorem zeroCount_zero (b : ℕ) (xs : List ℕ) : zeroCount b xs 0 = 0 := by
  simp [zeroCount]

theorem zeroCount_succ {b k : ℕ} {xs : List ℕ} (hk : k < xs.length) :
    zeroCount b xs (k + 1) = zeroCount b xs k +
      if digitZero b xs[k] then 1 else 0 := by
  rw [zeroCount, List.take_succ_eq_append_getElem hk, List.filter_append]
  by_cases h : digit b xs[k] = 0 <;> simp [zeroCount, digitZero, h]

/-! ## Zero-count program -/

/-- One block entry of the split-point count. -/
def countZeroSlot : Com :=
  .seq (.assign "rsv" (.get "xmem" (.add (.var "rslo") (.var "rsi"))))
    (.seq (.assign "rsd" (.shiftr (.var "rsv") (.var "rsb")))
      (.seq (.assign "rsd" (.and (.var "rsd") (.lit 1)))
        (.seq
          (.ite (.eq (.var "rsd") (.lit 0))
            (.assign "rsz" (.add (.var "rsz") (.lit 1))) .skip)
          (.assign "rsi" (.add (.var "rsi") (.lit 1))))))

/-- Count zero digits in the current block. -/
def countZeroCom : Com :=
  .seq (.assign "rsz" (.lit 0))
    (.seq (.assign "rsi" (.lit 0))
      (.while (.lt (.var "rsi") (.var "rsn")) countZeroSlot))

/-- Machine invariant for the touched-only counter. -/
def CountInv (na lo m b : ℕ) (X : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "rslo" = lo ∧ σ.vars "rsn" = m ∧ σ.vars "rsb" = b ∧
  σ.arrs "xmem" = arrOf na X ∧ σ.vars "rsi" ≤ m ∧
  σ.vars "rsz" = zeroCount b (segment lo m X) (σ.vars "rsi")

/-- The fixed body budget.  It includes both outcomes of the conditional. -/
def countZeroSlotK : ℕ := 64

theorem countZeroSlot_spec {B na lo m b : ℕ} {X : ℕ → ℕ}
    (hB : 1 < B) (hmB : m < B) (hbB : b < B)
    (hfit : lo + m ≤ na) (hword : lo + m < B)
    (hXB : ∀ i < m, X (lo + i) < B) :
    Spec B
      (fun σ => CountInv na lo m b X σ ∧ σ.vars "rsi" < m)
      countZeroSlot
      (fun σ σ' => CountInv na lo m b X σ' ∧
        σ'.vars "rsi" = σ.vars "rsi" + 1)
      countZeroSlotK := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hlo, hlen, hbit, hxmem, hile, hz⟩, hi⟩ := hσ
  let k := σ.vars "rsi"
  have hk : k < m := hi
  have hkB : k < B := lt_trans hk hmB
  have hidxna : lo + k < na := by omega
  have hidxB : lo + k < B := by omega
  have hxB : X (lo + k) < B := hXB k hk
  have hbvalB : X (lo + k) / 2 ^ b < B :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hxB
  have hdB : digit b (X (lo + k)) < B := by
    have := digit_lt b (X (lo + k))
    omega
  have hzle : σ.vars "rsz" ≤ k := by
    rw [hz]
    exact zeroCount_le _ _ _
  -- Load the current block entry.
  have e₁ : (Expr.get "xmem" (.add (.var "rslo") (.var "rsi"))).evalB B σ =
      some (X (lo + k)) := by
    apply evalB_get
    · have elo := evalB_var (B := B) (x := "rslo") (σ := σ) (by rw [hlo]; omega)
      have ei := evalB_var (B := B) (x := "rsi") (σ := σ) hkB
      simpa only [Bop.apply_add, hlo, k] using
        evalB_bin (op := .add) elo ei (by simpa [hlo, k] using hidxB)
    · rw [hxmem, show σ.vars "rsi" = k from rfl, getElem?_arrOf X hidxna]
    · exact hxB
  have r₁ := Run.assign (x := "rsv") e₁
  let σ₁ := σ.setVar "rsv" (X (lo + k))
  -- Shift to the selected digit.
  have e₂ : (Expr.shiftr (.var "rsv") (.var "rsb")).evalB B σ₁ =
      some (X (lo + k) / 2 ^ b) := by
    have ev : (Expr.var "rsv").evalB B σ₁ = some (X (lo + k)) :=
      evalB_var (by simp [σ₁, hxB])
    have eb : (Expr.var "rsb").evalB B σ₁ = some b := by
      simpa [σ₁, hbit] using
        (evalB_var (B := B) (x := "rsb") (σ := σ₁) (by simp [σ₁, hbit, hbB]))
    simpa only [Bop.apply_shiftr] using evalB_bin (op := .shiftr) ev eb hbvalB
  have r₂ := Run.assign (x := "rsd") e₂
  let σ₂ := σ₁.setVar "rsd" (X (lo + k) / 2 ^ b)
  -- Mask to one bit.
  have e₃ : (Expr.and (.var "rsd") (.lit 1)).evalB B σ₂ =
      some (digit b (X (lo + k))) := by
    have ed : (Expr.var "rsd").evalB B σ₂ = some (X (lo + k) / 2 ^ b) :=
      evalB_var (by simp [σ₂, hbvalB])
    have eone : (Expr.lit 1).evalB B σ₂ = some 1 := evalB_lit hB
    have hand := evalB_bin (op := .and) ed eone (by
      simpa only [Bop.apply_and, shiftr_and_one_eq_digit] using hdB)
    simpa only [Bop.apply_and, shiftr_and_one_eq_digit] using hand
  have r₃ := Run.assign (x := "rsd") e₃
  let σ₃ := σ₂.setVar "rsd" (digit b (X (lo + k)))
  have hguard : (Cond.eq (.var "rsd") (.lit 0)).evalB B σ₃ =
      some (digit b (X (lo + k)) == 0) :=
    evalB_condEq (evalB_var (by simp [σ₃, hdB])) (evalB_lit (by omega))
  by_cases hd0 : digit b (X (lo + k)) = 0
  · have hguard' : (Cond.eq (.var "rsd") (.lit 0)).evalB B σ₃ = some true := by
      rw [hguard, hd0]
      simp
    have hzlt : σ.vars "rsz" < B := lt_of_le_of_lt hzle hkB
    have ez : (Expr.add (.var "rsz") (.lit 1)).evalB B σ₃ =
        some (σ.vars "rsz" + 1) := by
      apply evalB_bin (op := .add)
      · apply evalB_var
        simpa [σ₃, σ₂, σ₁] using hzlt
      · exact evalB_lit (by omega)
      · simp only [Bop.apply_add]
        omega
    have r₄ := Run.assign (x := "rsz") ez
    let σ₄ := σ₃.setVar "rsz" (σ.vars "rsz" + 1)
    have ei : (Expr.add (.var "rsi") (.lit 1)).evalB B σ₄ = some (k + 1) := by
      apply evalB_bin (op := .add)
      · apply evalB_var
        simp [σ₄, σ₃, σ₂, σ₁, k, hkB]
      · exact evalB_lit (by omega)
      · simp only [Bop.apply_add]
        omega
    have r₅ := Run.assign (x := "rsi") ei
    let σ₅ := σ₄.setVar "rsi" (k + 1)
    refine ⟨σ₅, _, r₁.seq (r₂.seq (r₃.seq ((Run.ite_true hguard' r₄).seq r₅))), ?_, ?_, by
      simp [σ₅, k]⟩
    · norm_num [countZeroSlotK, Cond.size, Expr.size]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [σ₅, σ₄, σ₃, σ₂, σ₁, hlo]
      · simp [σ₅, σ₄, σ₃, σ₂, σ₁, hlen]
      · simp [σ₅, σ₄, σ₃, σ₂, σ₁, hbit]
      · simp [σ₅, σ₄, σ₃, σ₂, σ₁, hxmem]
      · simp [σ₅]
        omega
      · have hdz : digitZero b (X (lo + k)) = true := digitZero_eq_true.mpr hd0
        have hs := zeroCount_succ (b := b) (xs := segment lo m X)
          (k := k) (by simpa using hk)
        rw [segment_getElem lo m X k (by simpa using hk), hdz, if_pos rfl] at hs
        have hri₅ : σ₅.vars "rsi" = k + 1 := by simp [σ₅]
        have hrz₅ : σ₅.vars "rsz" = σ.vars "rsz" + 1 := by
          simp [σ₅, σ₄, σ₃, σ₂, σ₁]
        rw [hri₅, hrz₅, hz]
        exact hs.symm
  · have hd1 : digit b (X (lo + k)) = 1 :=
      (digit_eq_zero_or_one _ _).resolve_left hd0
    have hguard' : (Cond.eq (.var "rsd") (.lit 0)).evalB B σ₃ = some false := by
      rw [hguard, hd1]
      simp
    have ei : (Expr.add (.var "rsi") (.lit 1)).evalB B σ₃ = some (k + 1) := by
      apply evalB_bin (op := .add)
      · apply evalB_var
        simp [σ₃, σ₂, σ₁, k, hkB]
      · exact evalB_lit (by omega)
      · simp only [Bop.apply_add]
        omega
    have r₅ := Run.assign (x := "rsi") ei
    let σ₅ := σ₃.setVar "rsi" (k + 1)
    refine ⟨σ₅, _, r₁.seq (r₂.seq (r₃.seq ((Run.ite_false hguard' Run.skip).seq r₅))),
      ?_, ?_, by simp [σ₅, k]⟩
    · norm_num [countZeroSlotK, Cond.size, Expr.size]
    · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [σ₅, σ₃, σ₂, σ₁, hlo]
      · simp [σ₅, σ₃, σ₂, σ₁, hlen]
      · simp [σ₅, σ₃, σ₂, σ₁, hbit]
      · simp [σ₅, σ₃, σ₂, σ₁, hxmem]
      · simp [σ₅]
        omega
      · have hdz : digitZero b (X (lo + k)) = false := digitZero_eq_false.mpr hd1
        have hs := zeroCount_succ (b := b) (xs := segment lo m X)
          (k := k) (by simpa using hk)
        rw [segment_getElem lo m X k (by simpa using hk), hdz, if_neg (by decide)] at hs
        have hri₅ : σ₅.vars "rsi" = k + 1 := by simp [σ₅]
        have hrz₅ : σ₅.vars "rsz" = σ.vars "rsz" := by
          simp [σ₅, σ₃, σ₂, σ₁]
        rw [hri₅, hrz₅, hz]
        simpa using hs.symm

/-- The full split-point count.  The exact bound is linear in the block
length and independent of both `na` and the carrier. -/
theorem countZeroCom_spec {B na lo m b : ℕ} {X : ℕ → ℕ}
    (hB : 1 < B) (hmB : m < B) (hbB : b < B)
    (hfit : lo + m ≤ na) (hword : lo + m < B)
    (hXB : ∀ i < m, X (lo + i) < B) :
    Spec B
      (fun σ => σ.vars "rslo" = lo ∧ σ.vars "rsn" = m ∧
        σ.vars "rsb" = b ∧ σ.arrs "xmem" = arrOf na X)
      countZeroCom
      (fun _ σ' => CountInv na lo m b X σ' ∧ σ'.vars "rsi" = m ∧
        σ'.vars "rsz" = ((segment lo m X).filter (digitZero b)).length)
      ((countZeroSlotK + 4) * m + 8) := by
  intro σ hσ
  let σz := σ.setVar "rsz" 0
  have rz : Run B (.assign "rsz" (.lit 0)) σ σz 2 :=
    Run.assign (evalB_lit (by omega))
  have hpre : CountInv na lo m b X (σz.setVar "rsi" 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [σz, hσ.1]
    · simp [σz, hσ.2.1]
    · simp [σz, hσ.2.2.1]
    · simp [σz, hσ.2.2.2]
    · simp
    · simp [σz, zeroCount, String.ext_iff]
  have hrange := Spec.forRangeZero (B := B) "rsi" "rsn"
    (CountInv na lo m b X) m countZeroSlotK hmB
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.1)
    (countZeroSlot_spec hB hmB hbB hfit hword hXB)
  obtain ⟨σ', hrun, hI, hri⟩ := hrange.run (σ := σz) hpre
  refine ⟨σ', ?_, ?_⟩
  · simpa only [countZeroCom] using (rz.seq hrun).mono (by omega)
  · refine ⟨hI, hri, ?_⟩
    rw [hI.2.2.2.2.2, hri, zeroCount]
    have ht : (segment lo m X).take m = segment lo m X := by
      apply List.take_of_length_le
      simp
    rw [ht]

/-! ## Axiom audit -/

#print axioms countZeroSlot_spec
#print axioms countZeroCom_spec

end Lax3Proofs.Refine.CoverActiveRadixPass
