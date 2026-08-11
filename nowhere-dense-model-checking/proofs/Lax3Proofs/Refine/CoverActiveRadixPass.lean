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

/-! ## Stable selection into the scratch array

The executable pass uses two scans.  The first writes the zero-digit
subsequence at offset zero; the second writes the one-digit subsequence
immediately after it.  Each scan only visits the current block, so this
keeps the pass linear in the represented cover size rather than in the
ambient carrier for every block.
-/

/-- Boolean test used by one of the two stable selection scans. -/
def selected (want b x : ℕ) : Bool := decide (digit b x = want)

/-- Entries selected among the first `k` cells of a block segment. -/
def selectedPrefix (want b : ℕ) (xs : List ℕ) (k : ℕ) : List ℕ :=
  (xs.take k).filter (selected want b)

@[simp] theorem selected_zero (b x : ℕ) : selected 0 b x = digitZero b x := by
  simp [selected, digitZero]

@[simp] theorem selected_one (b x : ℕ) :
    selected 1 b x = !(digitZero b x) := by
  rcases digit_eq_zero_or_one b x with h | h <;> simp [selected, digitZero, h]

theorem selected_zero_fun (b : ℕ) : selected 0 b = digitZero b :=
  funext (selected_zero b)

theorem selected_one_fun (b : ℕ) : selected 1 b = fun x => !(digitZero b x) :=
  funext (selected_one b)

@[simp] theorem selectedPrefix_zero (want b : ℕ) (xs : List ℕ) :
    selectedPrefix want b xs 0 = [] := by
  simp [selectedPrefix]

theorem selectedPrefix_length_le (want b : ℕ) (xs : List ℕ) (k : ℕ) :
    (selectedPrefix want b xs k).length ≤ k := by
  exact le_trans (List.length_filter_le _ _) (List.length_take_le _ _)

theorem selectedPrefix_length_mono {want b k l : ℕ} {xs : List ℕ} (hkl : k ≤ l) :
    (selectedPrefix want b xs k).length ≤ (selectedPrefix want b xs l).length := by
  exact ((List.take_sublist_take_left hkl).filter (selected want b)).length_le

theorem selectedPrefix_succ_match {want b k : ℕ} {xs : List ℕ}
    (hk : k < xs.length) (hmatch : digit b xs[k] = want) :
    selectedPrefix want b xs (k + 1) =
      selectedPrefix want b xs k ++ [xs[k]] := by
  rw [selectedPrefix, List.take_succ_eq_append_getElem hk, List.filter_append]
  simp [selectedPrefix, selected, hmatch]

theorem selectedPrefix_succ_miss {want b k : ℕ} {xs : List ℕ}
    (hk : k < xs.length) (hmiss : digit b xs[k] ≠ want) :
    selectedPrefix want b xs (k + 1) = selectedPrefix want b xs k := by
  rw [selectedPrefix, List.take_succ_eq_append_getElem hk, List.filter_append]
  simp [selectedPrefix, selected, hmiss]

/-- Updating the cell just after a represented region represents the
same region with one final entry appended. -/
theorem upd_append_region {off v : ℕ} {Q : ℕ → ℕ} {ys : List ℕ}
    (hQ : ∀ j, (hj : j < ys.length) → Q (off + j) = ys[j]) :
    ∀ j, (hj : j < (ys ++ [v]).length) →
      upd Q (off + ys.length) v (off + j) = (ys ++ [v])[j] := by
  intro j hj
  have hjle : j ≤ ys.length := by simpa using hj
  rcases lt_or_eq_of_le hjle with hjlt | rfl
  · rw [upd_of_ne _ (by omega), List.getElem_append_left hjlt]
    exact hQ j hjlt
  · simp

/-- One entry of a stable selection scan. -/
def selectDigitSlot (want : ℕ) : Com :=
  .seq (.assign "rsv" (.get "xmem" (.add (.var "rslo") (.var "rsi"))))
    (.seq (.assign "rsd" (.shiftr (.var "rsv") (.var "rsb")))
      (.seq (.assign "rsd" (.and (.var "rsd") (.lit 1)))
        (.seq
          (.ite (.eq (.var "rsd") (.lit want))
            (.seq (.store "q" (.var "rsw") (.var "rsv"))
              (.assign "rsw" (.add (.var "rsw") (.lit 1))))
            .skip)
          (.assign "rsi" (.add (.var "rsi") (.lit 1))))))

/-- Scan the current block, appending the requested digit class at the
entering value of `rsw`. -/
def selectDigitCom (want : ℕ) : Com :=
  .seq (.assign "rsi" (.lit 0))
    (.while (.lt (.var "rsi") (.var "rsn")) (selectDigitSlot want))

/-- Machine invariant for one stable selection scan.  `Q₀` freezes the
scratch prefix below `off`, which is how the second scan preserves the
zero-digit half written by the first. -/
def SelectInv (n na lo m b want off : ℕ) (X Q₀ : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "rslo" = lo ∧ σ.vars "rsn" = m ∧ σ.vars "rsb" = b ∧
  σ.arrs "xmem" = arrOf na X ∧ σ.vars "rsi" ≤ m ∧
  ∃ Q : ℕ → ℕ,
    σ.arrs "q" = arrOf n Q ∧
    σ.vars "rsw" = off +
      (selectedPrefix want b (segment lo m X) (σ.vars "rsi")).length ∧
    (∀ j < off, Q j = Q₀ j) ∧
    ∀ j, (hj : j <
        (selectedPrefix want b (segment lo m X) (σ.vars "rsi")).length) →
      Q (off + j) =
        (selectedPrefix want b (segment lo m X) (σ.vars "rsi"))[j]

/-- A generous fixed budget covering both branches of one selection
turn. -/
def selectDigitSlotK : ℕ := 96

theorem selectDigitSlot_spec {B n na lo m b want off : ℕ} {X Q₀ : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B) (hmn : m ≤ n) (hbB : b < B)
    (hwantB : want < B) (hfit : lo + m ≤ na) (hword : lo + m < B)
    (hXB : ∀ i < m, X (lo + i) < B)
    (hcap : off + (selectedPrefix want b (segment lo m X) m).length ≤ n) :
    Spec B
      (fun σ => SelectInv n na lo m b want off X Q₀ σ ∧ σ.vars "rsi" < m)
      (selectDigitSlot want)
      (fun σ σ' => SelectInv n na lo m b want off X Q₀ σ' ∧
        σ'.vars "rsi" = σ.vars "rsi" + 1)
      selectDigitSlotK := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hlo, hlen, hbit, hxmem, hile, Q, hq, hrsw, hbefore, hcells⟩, hi⟩ := hσ
  let k := σ.vars "rsi"
  let xs := segment lo m X
  let ys := selectedPrefix want b xs k
  have hk : k < m := hi
  have hkB : k < B := lt_of_lt_of_le (lt_trans hk (lt_of_le_of_lt hmn hnB))
    (Nat.le_refl B)
  have hidxna : lo + k < na := by omega
  have hidxB : lo + k < B := by omega
  have hxB : X (lo + k) < B := hXB k hk
  have hbvalB : X (lo + k) / 2 ^ b < B :=
    lt_of_le_of_lt (Nat.div_le_self _ _) hxB
  have hdB : digit b (X (lo + k)) < B := by
    have := digit_lt b (X (lo + k))
    omega
  have hkxs : k < xs.length := by simpa [xs] using hk
  have hxsval : xs[k] = X (lo + k) := by simp [xs]
  -- Read the current value and its selected digit.
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
  have hguard : (Cond.eq (.var "rsd") (.lit want)).evalB B σ₃ =
      some (digit b (X (lo + k)) == want) :=
    evalB_condEq (evalB_var (by simp [σ₃, hdB])) (evalB_lit hwantB)
  by_cases hmatch : digit b (X (lo + k)) = want
  · have hguard' : (Cond.eq (.var "rsd") (.lit want)).evalB B σ₃ = some true := by
      rw [hguard, hmatch]
      simp
    have hs : selectedPrefix want b xs (k + 1) = ys ++ [X (lo + k)] := by
      have hm : digit b xs[k] = want := by rw [hxsval]; exact hmatch
      simpa [ys, hxsval] using selectedPrefix_succ_match hkxs hm
    have hmono : (ys ++ [X (lo + k)]).length ≤
        (selectedPrefix want b xs m).length := by
      rw [← hs]
      exact selectedPrefix_length_mono (by omega)
    have hwriteN : off + ys.length < n := by
      have hcap' : off + (selectedPrefix want b xs m).length ≤ n := by
        simpa [xs] using hcap
      simp only [List.length_append, List.length_singleton] at hmono
      omega
    have hwriteB : off + ys.length < B := lt_trans hwriteN hnB
    have hrsw₃ : σ₃.vars "rsw" = off + ys.length := by
      simpa [σ₃, σ₂, σ₁, ys, xs, k] using hrsw
    have eiw : (Expr.var "rsw").evalB B σ₃ = some (off + ys.length) := by
      simpa [hrsw₃] using
        (evalB_var (B := B) (x := "rsw") (σ := σ₃) (by rw [hrsw₃]; exact hwriteB))
    have ev : (Expr.var "rsv").evalB B σ₃ = some (X (lo + k)) := by
      apply evalB_var
      simp [σ₃, σ₂, σ₁, hxB]
    have r₄ := Run.store (a := "q") eiw ev (by
      simp [σ₃, σ₂, σ₁, hq, hwriteN])
    let σ₄ := σ₃.setArr "q" (off + ys.length) (X (lo + k))
    have hrsw₄ : σ₄.vars "rsw" = off + ys.length := by simp [σ₄, hrsw₃]
    have erw : (Expr.add (.var "rsw") (.lit 1)).evalB B σ₄ =
        some (off + ys.length + 1) := by
      apply evalB_bin (op := .add)
      · simpa [hrsw₄] using
          (evalB_var (B := B) (x := "rsw") (σ := σ₄) (by rw [hrsw₄]; exact hwriteB))
      · exact evalB_lit (by omega)
      · simp only [Bop.apply_add]
        have : off + ys.length + 1 ≤ n := by omega
        omega
    have r₅ := Run.assign (x := "rsw") erw
    let σ₅ := σ₄.setVar "rsw" (off + ys.length + 1)
    have eri : (Expr.add (.var "rsi") (.lit 1)).evalB B σ₅ = some (k + 1) := by
      apply evalB_bin (op := .add)
      · apply evalB_var
        simp [σ₅, σ₄, σ₃, σ₂, σ₁, k, hkB]
      · exact evalB_lit (by omega)
      · simp only [Bop.apply_add]
        omega
    have r₆ := Run.assign (x := "rsi") eri
    let σ₆ := σ₅.setVar "rsi" (k + 1)
    refine ⟨σ₆, _,
      r₁.seq (r₂.seq (r₃.seq ((Run.ite_true hguard' (r₄.seq r₅)).seq r₆))), ?_, ?_,
      by simp [σ₆, k]⟩
    · norm_num [selectDigitSlotK, Cond.size, Expr.size]
    · refine ⟨?_, ?_, ?_, ?_, ?_, upd Q (off + ys.length) (X (lo + k)), ?_, ?_, ?_, ?_⟩
      · simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hlo]
      · simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hlen]
      · simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hbit]
      · simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hxmem]
      · simp [σ₆]
        omega
      · rw [arrs_setVar, arrs_setVar, arrs_setArr, if_pos rfl, arrs_setVar,
          arrs_setVar, arrs_setVar, hq, set_arrOf_eq_upd]
      · have hri : σ₆.vars "rsi" = k + 1 := by simp [σ₆]
        rw [hri, show selectedPrefix want b (segment lo m X) (k + 1) =
          ys ++ [X (lo + k)] from by simpa [xs] using hs]
        simp [σ₆, σ₅]
        omega
      · intro j hj
        rw [upd_of_ne _ (by omega)]
        exact hbefore j hj
      · have hri : σ₆.vars "rsi" = k + 1 := by simp [σ₆]
        rw [hri, show selectedPrefix want b (segment lo m X) (k + 1) =
          ys ++ [X (lo + k)] from by simpa [xs] using hs]
        exact upd_append_region hcells
  · have hguard' : (Cond.eq (.var "rsd") (.lit want)).evalB B σ₃ = some false := by
      rw [hguard]
      simp [hmatch]
    have hs : selectedPrefix want b xs (k + 1) = ys := by
      have hm : digit b xs[k] ≠ want := by rw [hxsval]; exact hmatch
      simpa [ys] using selectedPrefix_succ_miss hkxs hm
    have eri : (Expr.add (.var "rsi") (.lit 1)).evalB B σ₃ = some (k + 1) := by
      apply evalB_bin (op := .add)
      · apply evalB_var
        simp [σ₃, σ₂, σ₁, k, hkB]
      · exact evalB_lit (by omega)
      · simp only [Bop.apply_add]
        omega
    have r₆ := Run.assign (x := "rsi") eri
    let σ₆ := σ₃.setVar "rsi" (k + 1)
    refine ⟨σ₆, _, r₁.seq (r₂.seq (r₃.seq ((Run.ite_false hguard' Run.skip).seq r₆))),
      ?_, ?_, by simp [σ₆, k]⟩
    · norm_num [selectDigitSlotK, Cond.size, Expr.size]
    · refine ⟨?_, ?_, ?_, ?_, ?_, Q, ?_, ?_, ?_, ?_⟩
      · simp [σ₆, σ₃, σ₂, σ₁, hlo]
      · simp [σ₆, σ₃, σ₂, σ₁, hlen]
      · simp [σ₆, σ₃, σ₂, σ₁, hbit]
      · simp [σ₆, σ₃, σ₂, σ₁, hxmem]
      · simp [σ₆]
        omega
      · simp [σ₆, σ₃, σ₂, σ₁, hq]
      · have hri : σ₆.vars "rsi" = k + 1 := by simp [σ₆]
        rw [hri, show selectedPrefix want b (segment lo m X) (k + 1) = ys from by
          simpa [xs] using hs]
        simpa [σ₆, σ₃, σ₂, σ₁, ys, xs, k] using hrsw
      · exact hbefore
      · have hri : σ₆.vars "rsi" = k + 1 := by simp [σ₆]
        rw [hri, show selectedPrefix want b (segment lo m X) (k + 1) = ys from by
          simpa [xs] using hs]
        exact hcells

/-- A complete stable selection scan.  The prefix below its starting
offset is framed, and the selected entries occupy the next consecutive
cells in their entering order. -/
theorem selectDigitCom_spec {B n na lo m b want off : ℕ} {X Q₀ : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B) (hmn : m ≤ n) (hbB : b < B)
    (hwantB : want < B) (hfit : lo + m ≤ na) (hword : lo + m < B)
    (hXB : ∀ i < m, X (lo + i) < B)
    (hcap : off + (selectedPrefix want b (segment lo m X) m).length ≤ n) :
    Spec B
      (fun σ => σ.vars "rslo" = lo ∧ σ.vars "rsn" = m ∧
        σ.vars "rsb" = b ∧ σ.arrs "xmem" = arrOf na X ∧
        σ.arrs "q" = arrOf n Q₀ ∧ σ.vars "rsw" = off)
      (selectDigitCom want)
      (fun _ σ' => SelectInv n na lo m b want off X Q₀ σ' ∧
        σ'.vars "rsi" = m)
      ((selectDigitSlotK + 4) * m + 6) := by
  have hmB : m < B := lt_of_le_of_lt hmn hnB
  have hbody := selectDigitSlot_spec (X := X) (Q₀ := Q₀)
    hB hnB hmn hbB hwantB hfit hword hXB hcap
  have hscan := Spec.forRangeZero (B := B) "rsi" "rsn"
    (SelectInv n na lo m b want off X Q₀) m selectDigitSlotK hmB
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.1) hbody
  refine hscan.pre ?_
  rintro σ ⟨hlo, hlen, hbit, hxmem, hq, hrsw⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, Q₀, ?_, ?_, ?_, ?_⟩
  · simp [hlo]
  · simp [hlen]
  · simp [hbit]
  · simp [hxmem]
  · simp
  · simp [hq]
  · simp [hrsw, selectedPrefix]
  · intro j hj
    rfl
  · intro j hj
    simp [selectedPrefix] at hj

/-! ## The complete stable scatter -/

theorem selectedPrefix_partition_length (b : ℕ) (xs : List ℕ) :
    (selectedPrefix 0 b xs xs.length).length +
      (selectedPrefix 1 b xs xs.length).length = xs.length := by
  have hlen := (radixPass_perm b xs).length_eq
  simp only [selectedPrefix, List.take_length]
  rw [selected_zero_fun, selected_one_fun]
  simpa only [radixPass, List.length_append] using hlen

/-- Two adjacent represented regions represent their concatenation. -/
theorem adjacent_regions_append {Q : ℕ → ℕ} {as bs : List ℕ}
    (ha : ∀ j, (hj : j < as.length) → Q j = as[j])
    (hb : ∀ j, (hj : j < bs.length) → Q (as.length + j) = bs[j]) :
    ∀ j, (hj : j < (as ++ bs).length) → Q j = (as ++ bs)[j] := by
  intro j hj
  by_cases hja : j < as.length
  · rw [List.getElem_append_left hja]
    exact ha j hja
  · have hjb : j - as.length < bs.length := by
      simp only [List.length_append] at hj
      omega
    rw [List.getElem_append_right (by omega)]
    have hcell := hb (j - as.length) hjb
    simpa [Nat.add_sub_of_le (Nat.le_of_not_gt hja)] using hcell

/-- Zero entries are selected first from offset zero; the final write
pointer is then exactly the start offset for the stable one-entry scan. -/
def stableScatterCom : Com :=
  .seq (.assign "rsw" (.lit 0))
    (.seq (selectDigitCom 0) (selectDigitCom 1))

def selectDigitCost (m : ℕ) : ℕ := (selectDigitSlotK + 4) * m + 6

def stableScatterCost (m : ℕ) : ℕ := 2 + selectDigitCost m + selectDigitCost m

/-- Output contract of the stable scatter: the first `m` scratch cells
are exactly the mathematical radix pass of the entering block. -/
def StableScatterOut (n na lo m b : ℕ) (X : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "rslo" = lo ∧ σ.vars "rsn" = m ∧ σ.vars "rsb" = b ∧
  σ.arrs "xmem" = arrOf na X ∧
  ∃ Q : ℕ → ℕ, σ.arrs "q" = arrOf n Q ∧
    ∀ j, (hj : j < m) →
      Q j = (radixPass b (segment lo m X))[j]'(by
        rw [(radixPass_perm b (segment lo m X)).length_eq, segment_length]
        exact hj)

theorem stableScatterCom_spec {B n na lo m b : ℕ} {X Q₀ : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B) (hmn : m ≤ n) (hbB : b < B)
    (hfit : lo + m ≤ na) (hword : lo + m < B)
    (hXB : ∀ i < m, X (lo + i) < B) :
    Spec B
      (fun σ => σ.vars "rslo" = lo ∧ σ.vars "rsn" = m ∧
        σ.vars "rsb" = b ∧ σ.arrs "xmem" = arrOf na X ∧
        σ.arrs "q" = arrOf n Q₀)
      stableScatterCom
      (fun _ σ' => StableScatterOut n na lo m b X σ')
      (stableScatterCost m) := by
  intro σ hσ
  obtain ⟨hlo, hlen, hbit, hxmem, hq⟩ := hσ
  let xs := segment lo m X
  let zs := selectedPrefix 0 b xs m
  let os := selectedPrefix 1 b xs m
  have hxslen : xs.length = m := by simp [xs]
  have hpart : zs.length + os.length = m := by
    have h := selectedPrefix_partition_length b xs
    rw [hxslen] at h
    simpa [zs, os] using h
  have hzcap : 0 + (selectedPrefix 0 b (segment lo m X) m).length ≤ n := by
    have hzle := selectedPrefix_length_le 0 b (segment lo m X) m
    omega
  let σ₀ := σ.setVar "rsw" 0
  have r₀ : Run B (.assign "rsw" (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  obtain ⟨σz, rz, hIz, hiz⟩ :=
    (selectDigitCom_spec (X := X) (Q₀ := Q₀) hB hnB hmn hbB (by omega)
      hfit hword hXB hzcap).run (σ := σ₀) ⟨by simp [σ₀, hlo], by simp [σ₀, hlen],
        by simp [σ₀, hbit], by simp [σ₀, hxmem], by simp [σ₀, hq], by simp [σ₀]⟩
  obtain ⟨hzlo, hzlen, hzbit, hzxmem, -, Qz, hqz, hrswz, -, hcellz⟩ := hIz
  have hrswz' : σz.vars "rsw" = zs.length := by
    rw [hrswz, hiz]
    simp [zs, xs]
  have hocap : zs.length +
      (selectedPrefix 1 b (segment lo m X) m).length ≤ n := by
    simpa [os, xs] using (show zs.length + os.length ≤ n by omega)
  obtain ⟨σo, ro, hIo, hio⟩ :=
    (selectDigitCom_spec (X := X) (Q₀ := Qz) hB hnB hmn hbB (by omega)
      hfit hword hXB hocap).run (σ := σz)
      ⟨hzlo, hzlen, hzbit, hzxmem, hqz, hrswz'⟩
  obtain ⟨holo, holen, hobit, hoxmem, -, Qo, hqo, -, hbeforeo, hcello⟩ := hIo
  have hzcell : ∀ j, (hj : j < zs.length) → Qz j = zs[j] := by
    intro j hj
    have h := hcellz j (by simpa [hiz, zs, xs] using hj)
    simpa [hiz, zs, xs] using h
  have hocell : ∀ j, (hj : j < os.length) → Qo (zs.length + j) = os[j] := by
    intro j hj
    have h := hcello j (by simpa [hio, os, xs] using hj)
    simpa [hio, os, xs] using h
  have hzero : ∀ j, (hj : j < zs.length) → Qo j = zs[j] := by
    intro j hj
    rw [hbeforeo j hj]
    exact hzcell j hj
  have hregions := adjacent_regions_append hzero hocell
  have hradix : zs ++ os = radixPass b xs := by
    have htake : xs.take m = xs := by
      rw [← hxslen]
      exact List.take_length
    simp only [zs, os, selectedPrefix, htake, radixPass]
    rw [selected_zero_fun, selected_one_fun]
  refine ⟨σo, ?_, ⟨holo, holen, hobit, hoxmem, Qo, hqo, ?_⟩⟩
  · simpa [stableScatterCom, stableScatterCost, selectDigitCost] using
      (r₀.seq (rz.seq ro)).mono (by omega)
  · intro j hj
    have hj' : j < (zs ++ os).length := by
      simp only [List.length_append]
      omega
    have h := hregions j hj'
    simpa [hradix, xs] using h

/-! ## Copying the scratch prefix back into the block -/

/-- Replace the first `k` cells of the segment at `lo` by the first
`k` cells of `Q`, leaving every other arena cell unchanged. -/
def pastePrefix (lo k : ℕ) (X Q : ℕ → ℕ) (p : ℕ) : ℕ :=
  if lo ≤ p ∧ p < lo + k then Q (p - lo) else X p

@[simp] theorem pastePrefix_zero (lo : ℕ) (X Q : ℕ → ℕ) :
    pastePrefix lo 0 X Q = X := by
  funext p
  simp [pastePrefix]

@[simp] theorem pastePrefix_at {lo k j : ℕ} {X Q : ℕ → ℕ} (hj : j < k) :
    pastePrefix lo k X Q (lo + j) = Q j := by
  simp [pastePrefix, hj]

theorem pastePrefix_outside {lo k p : ℕ} {X Q : ℕ → ℕ}
    (hp : p < lo ∨ lo + k ≤ p) : pastePrefix lo k X Q p = X p := by
  simp only [pastePrefix]
  split <;> omega

/-- A store at the next segment cell extends the pasted prefix by one. -/
theorem upd_pastePrefix_current (lo k : ℕ) (X Q : ℕ → ℕ) :
    upd (pastePrefix lo k X Q) (lo + k) (Q k) =
      pastePrefix lo (k + 1) X Q := by
  funext p
  rw [upd_apply]
  by_cases hp : p = lo + k
  · subst p
    simp [pastePrefix]
  · by_cases hold : lo ≤ p ∧ p < lo + k
    · have hnew : lo ≤ p ∧ p < lo + (k + 1) := by omega
      simp [pastePrefix, hp, hold, hnew]
    · have hnew : ¬(lo ≤ p ∧ p < lo + (k + 1)) := by
        intro h
        omega
      simp [pastePrefix, hp, hold, hnew]

/-- One cell copied from the scratch prefix back to the block segment. -/
def copyBackSlot : Com :=
  .seq (.assign "rsv" (.get "q" (.var "rsi")))
    (.seq (.store "xmem" (.add (.var "rslo") (.var "rsi")) (.var "rsv"))
      (.assign "rsi" (.add (.var "rsi") (.lit 1))))

def copyBackCom : Com :=
  .seq (.assign "rsi" (.lit 0))
    (.while (.lt (.var "rsi") (.var "rsn")) copyBackSlot)

def CopyBackInv (n na lo m b : ℕ) (X Q : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "rslo" = lo ∧ σ.vars "rsn" = m ∧ σ.vars "rsb" = b ∧
  σ.arrs "q" = arrOf n Q ∧ σ.vars "rsi" ≤ m ∧
  σ.arrs "xmem" = arrOf na (pastePrefix lo (σ.vars "rsi") X Q)

def copyBackSlotK : ℕ := 32

theorem copyBackSlot_spec {B n na lo m b : ℕ} {X Q : ℕ → ℕ}
    (hnB : n < B) (hmn : m ≤ n) (hfit : lo + m ≤ na)
    (hword : lo + m < B) (hQB : ∀ i < m, Q i < B) :
    Spec B
      (fun σ => CopyBackInv n na lo m b X Q σ ∧ σ.vars "rsi" < m)
      copyBackSlot
      (fun σ σ' => CopyBackInv n na lo m b X Q σ' ∧
        σ'.vars "rsi" = σ.vars "rsi" + 1)
      copyBackSlotK := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨⟨hlo, hlen, hbit, hq, hile, hxmem⟩, hi⟩ := hσ
  let k := σ.vars "rsi"
  have hk : k < m := hi
  have hkB : k < B := by omega
  have hkn : k < n := lt_of_lt_of_le hk hmn
  have hidxna : lo + k < na := by omega
  have hidxB : lo + k < B := by omega
  have hqB : Q k < B := hQB k hk
  have eqread : (Expr.get "q" (.var "rsi")).evalB B σ = some (Q k) := by
    apply evalB_get
    · exact evalB_var hkB
    · rw [hq, show σ.vars "rsi" = k from rfl, getElem?_arrOf Q hkn]
    · exact hqB
  have r₁ := Run.assign (x := "rsv") eqread
  let σ₁ := σ.setVar "rsv" (Q k)
  have eidx : (Expr.add (.var "rslo") (.var "rsi")).evalB B σ₁ = some (lo + k) := by
    have elo : (Expr.var "rslo").evalB B σ₁ = some lo := by
      simpa [σ₁, hlo] using
        (evalB_var (B := B) (x := "rslo") (σ := σ₁) (by simp [σ₁, hlo]; omega))
    have eki : (Expr.var "rsi").evalB B σ₁ = some k := by
      simpa [σ₁, k] using
        (evalB_var (B := B) (x := "rsi") (σ := σ₁) (by simp [σ₁, k, hkB]))
    simpa only [Bop.apply_add] using evalB_bin (op := .add) elo eki hidxB
  have evalv : (Expr.var "rsv").evalB B σ₁ = some (Q k) :=
    evalB_var (by simp [σ₁, hqB])
  have r₂ := Run.store (a := "xmem") eidx evalv (by
    simp [σ₁, hxmem, hidxna])
  let σ₂ := σ₁.setArr "xmem" (lo + k) (Q k)
  have einc : (Expr.add (.var "rsi") (.lit 1)).evalB B σ₂ = some (k + 1) := by
    apply evalB_bin (op := .add)
    · apply evalB_var
      simp [σ₂, σ₁, k, hkB]
    · exact evalB_lit (by omega)
    · simp only [Bop.apply_add]
      omega
  have r₃ := Run.assign (x := "rsi") einc
  let σ₃ := σ₂.setVar "rsi" (k + 1)
  refine ⟨σ₃, _, r₁.seq (r₂.seq r₃), ?_, ?_, by simp [σ₃, k]⟩
  · norm_num [copyBackSlotK, Expr.size]
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [σ₃, σ₂, σ₁, hlo]
    · simp [σ₃, σ₂, σ₁, hlen]
    · simp [σ₃, σ₂, σ₁, hbit]
    · simp [σ₃, σ₂, σ₁, hq]
    · simp [σ₃]
      omega
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, arrs_setVar, hxmem,
        set_arrOf_eq_upd, upd_pastePrefix_current]
      simp [σ₃, k]

theorem copyBackCom_spec {B n na lo m b : ℕ} {X Q : ℕ → ℕ}
    (hnB : n < B) (hmn : m ≤ n) (hfit : lo + m ≤ na)
    (hword : lo + m < B) (hQB : ∀ i < m, Q i < B) :
    Spec B
      (fun σ => σ.vars "rslo" = lo ∧ σ.vars "rsn" = m ∧
        σ.vars "rsb" = b ∧ σ.arrs "q" = arrOf n Q ∧
        σ.arrs "xmem" = arrOf na X)
      copyBackCom
      (fun _ σ' => CopyBackInv n na lo m b X Q σ' ∧ σ'.vars "rsi" = m)
      ((copyBackSlotK + 4) * m + 6) := by
  have hmB : m < B := lt_of_le_of_lt hmn hnB
  have hscan := Spec.forRangeZero (B := B) "rsi" "rsn"
    (CopyBackInv n na lo m b X Q) m copyBackSlotK hmB
    (fun _ h => h.2.2.2.2.1) (fun _ h => h.2.1)
    (copyBackSlot_spec hnB hmn hfit hword hQB)
  refine hscan.pre ?_
  rintro σ ⟨hlo, hlen, hbit, hq, hxmem⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hlo]
  · simp [hlen]
  · simp [hbit]
  · simp [hq]
  · simp
  · simp [hxmem]

/-! ## One executable radix pass -/

def radixPassCom : Com := .seq stableScatterCom copyBackCom

def radixPassCost (m : ℕ) : ℕ :=
  stableScatterCost m + ((copyBackSlotK + 4) * m + 6)

/-- The pass replaces exactly one block by its mathematical stable
radix pass and leaves the rest of the arena untouched.  The scratch
array remains allocated for the next bit. -/
def RadixPassOut (n na lo m b : ℕ) (X : ℕ → ℕ) (σ : Env) : Prop :=
  σ.vars "rslo" = lo ∧ σ.vars "rsn" = m ∧ σ.vars "rsb" = b ∧
  ∃ X' Q : ℕ → ℕ,
    σ.arrs "xmem" = arrOf na X' ∧ σ.arrs "q" = arrOf n Q ∧
    segment lo m X' = radixPass b (segment lo m X) ∧
    ∀ p, p < lo ∨ lo + m ≤ p → X' p = X p

theorem stableScratch_words {B lo m b : ℕ} {X Q : ℕ → ℕ}
    (hXB : ∀ i < m, X (lo + i) < B)
    (hQ : ∀ j, (hj : j < m) →
      Q j = (radixPass b (segment lo m X))[j]'(by
        rw [(radixPass_perm b (segment lo m X)).length_eq, segment_length]
        exact hj)) :
    ∀ j < m, Q j < B := by
  intro j hj
  rw [hQ j hj]
  have hjr : j < (radixPass b (segment lo m X)).length := by
    rw [(radixPass_perm b (segment lo m X)).length_eq, segment_length]
    exact hj
  have hmemr := List.getElem_mem hjr
  have hmemx : (radixPass b (segment lo m X))[j] ∈ segment lo m X :=
    (radixPass_perm b (segment lo m X)).mem_iff.mp hmemr
  obtain ⟨i, hi, heq⟩ := mem_segment_iff.mp hmemx
  rw [← heq]
  exact hXB i hi

theorem radixPassCom_spec {B n na lo m b : ℕ} {X Q₀ : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B) (hmn : m ≤ n) (hbB : b < B)
    (hfit : lo + m ≤ na) (hword : lo + m < B)
    (hXB : ∀ i < m, X (lo + i) < B) :
    Spec B
      (fun σ => σ.vars "rslo" = lo ∧ σ.vars "rsn" = m ∧
        σ.vars "rsb" = b ∧ σ.arrs "xmem" = arrOf na X ∧
        σ.arrs "q" = arrOf n Q₀)
      radixPassCom
      (fun _ σ' => RadixPassOut n na lo m b X σ')
      (radixPassCost m) := by
  intro σ hσ
  obtain ⟨σs, rs, hsout⟩ :=
    (stableScatterCom_spec (X := X) (Q₀ := Q₀) hB hnB hmn hbB hfit hword hXB).run
      (σ := σ) hσ
  obtain ⟨hslo, hslen, hsbit, hsxmem, Q, hsq, hQcell⟩ := hsout
  have hQB : ∀ j < m, Q j < B := stableScratch_words hXB hQcell
  obtain ⟨σc, rc, hIc, hri⟩ :=
    (copyBackCom_spec (X := X) (Q := Q) hnB hmn hfit hword hQB).run
      (σ := σs) ⟨hslo, hslen, hsbit, hsq, hsxmem⟩
  obtain ⟨hclo, hclen, hcbit, hcq, -, hcxmem⟩ := hIc
  let X' := pastePrefix lo m X Q
  have hxmem' : σc.arrs "xmem" = arrOf na X' := by
    rw [hcxmem, hri]
  have hseg : segment lo m X' = radixPass b (segment lo m X) := by
    apply List.ext_getElem
    · rw [(radixPass_perm b (segment lo m X)).length_eq]
      simp
    · intro j hj₁ hj₂
      have hjm : j < m := by simpa using hj₁
      rw [segment_getElem lo m X' j hj₁,
        show X' (lo + j) = Q j from by simp [X', hjm]]
      exact hQcell j hjm
  refine ⟨σc, ?_, ⟨hclo, hclen, hcbit, X', Q, hxmem', hcq, hseg, ?_⟩⟩
  · simpa [radixPassCom, radixPassCost] using (rs.seq rc)
  · intro p hp
    exact pastePrefix_outside hp

/-! ## Axiom audit -/

#print axioms countZeroSlot_spec
#print axioms countZeroCom_spec
#print axioms selectDigitSlot_spec
#print axioms selectDigitCom_spec
#print axioms stableScatterCom_spec
#print axioms copyBackSlot_spec
#print axioms copyBackCom_spec
#print axioms radixPassCom_spec

end Lax3Proofs.Refine.CoverActiveRadixPass
