import Lax185574Proofs.Conversions.Ram.Reach

/-!
Flags of pairs of parts.

With the labels of a partition in the array `cur`, `flagScan F c` scans
all ordered pairs `(x, y)` of distinct vertices and sets entry
`(lo, hi)` of the matrix `F` to `1` when the condition `c` holds for the
pair, where `lo ≤ hi` are the labels of `x` and `y`. It uses the scalars
`x`, `y`, `a`, `b`, `lo` and `hi`.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- The labels of `x` and `y`, ordered, into `lo` and `hi`. -/
def lohi : Com :=
  .seq (.assign "a" (.get "cur" (.var "x"))) (.seq (.assign "b" (.get "cur" (.var "y")))
    (.ite (.lt (.var "a") (.var "b")) (.seq (.assign "lo" (.var "a")) (.assign "hi" (.var "b")))
      (.seq (.assign "lo" (.var "b")) (.assign "hi" (.var "a")))))

theorem lohi_run {B n : ℕ} {lab : ℕ → ℕ} {τ : Env} (hv : Vec τ "cur" n lab)
    (hlab : ∀ z < n, lab z < n) (hnB : n < B) {i j : ℕ} (hx : τ.vars "x" = i)
    (hy : τ.vars "y" = j) (hi : i < n) (hj : j < n) :
    ∃ τ', Run B lohi τ τ' 20 ∧ τ'.vars "lo" = min (lab i) (lab j) ∧
      τ'.vars "hi" = max (lab i) (lab j) ∧ τ'.arrs = τ.arrs ∧ τ'.inp = τ.inp ∧ τ'.out = τ.out ∧
      ∀ z, z ∉ ["a", "b", "lo", "hi"] → τ'.vars z = τ.vars z := by
  have hli := hlab i hi
  have hlj := hlab j hj
  set τ2 := (τ.setVar "a" (lab i)).setVar "b" (lab j) with hτ2
  have e1 := hv.evalB (B := B) hx hi (by omega) (by omega)
  have e2 := Vec.evalB (B := B) (τ := τ.setVar "a" (lab i)) (x := "y") (hv.of_eq (by simp))
    (by simp [hy]) hj (by omega) (by omega)
  by_cases hab : lab i < lab j
  · refine ⟨(τ2.setVar "lo" (lab i)).setVar "hi" (lab j), ?_, by simp [Nat.min_eq_left hab.le],
      by simp [Nat.max_eq_right hab.le], by simp [hτ2], by simp [hτ2], by simp [hτ2], ?_⟩
    · refine (Run.seq (Run.assign e1) (Run.seq (Run.assign e2)
        (Run.ite_true ?_ (Run.seq (Run.assign (by simp; omega)) (Run.assign (by simp; omega)))))).mono
        (by simp)
      rw [evalB_condLt (evalB_var (by simp [hτ2]; omega)) (evalB_var (by simp [hτ2]; omega))]
      simp [hτ2, hab]
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp [hτ2, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]
  · refine ⟨(τ2.setVar "lo" (lab j)).setVar "hi" (lab i), ?_, by simp; omega,
      by simp; omega, by simp [hτ2], by simp [hτ2], by simp [hτ2], ?_⟩
    · refine (Run.seq (Run.assign e1) (Run.seq (Run.assign e2)
        (Run.ite_false ?_ (Run.seq (Run.assign (by simp; omega)) (Run.assign (by simp; omega)))))).mono
        (by simp)
      rw [evalB_condLt (evalB_var (by simp [hτ2]; omega)) (evalB_var (by simp [hτ2]; omega))]
      simp [hτ2, hab]
    · intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      simp [hτ2, hz.1, hz.2.1, hz.2.2.1, hz.2.2.2]

/-- Some pair of distinct vertices with labels `lo ≤ hi` has the
property `P`. -/
def FlagP (n : ℕ) (lab : ℕ → ℕ) (P : ℕ → ℕ → Prop) (lo hi : ℕ) : Prop :=
  ∃ x < n, ∃ y < n, x ≠ y ∧ min (lab x) (lab y) = lo ∧ max (lab x) (lab y) = hi ∧ P x y

/-- One pair of the scan. -/
def flagStep (F : String) (c : Cond) : Com :=
  .ite (.eq (.var "x") (.var "y")) .skip
    (.seq lohi (.ite c (.store F (rm "lo" "hi") (.lit 1)) .skip))

/-- Scan all pairs. -/
def flagScan (F : String) (c : Cond) : Com :=
  forUp "x" (.var "n") (forUp "y" (.var "n") (flagStep F c))

/-- **Flags of pairs of parts.** `Ctx` must survive the scalars of the
scan and stores into `F`. -/
theorem flagScan_run {B n : ℕ} {F : String} {c : Cond} (Ctx : Env → Prop) (lab : ℕ → ℕ)
    (P : ℕ → ℕ → Prop) (hB : n * n + n + 1 < B) (hlab : ∀ z < n, lab z < n)
    (hCn : ∀ τ, Ctx τ → τ.vars "n" = n) (hCc : ∀ τ, Ctx τ → Vec τ "cur" n lab)
    (hCv : ∀ τ x v, x ∈ ["x", "y", "a", "b", "lo", "hi"] → Ctx τ → Ctx (τ.setVar x v))
    (hCe : ∀ τ τ', Ctx τ → τ'.arrs = τ.arrs → τ'.inp = τ.inp → τ'.out = τ.out →
      (∀ z, z ∉ ["a", "b", "lo", "hi"] → τ'.vars z = τ.vars z) → Ctx τ')
    (hCs : ∀ τ i v, Ctx τ → Ctx (τ.setArr F i v))
    (hc : ∀ τ i j, Ctx τ → τ.vars "x" = i → τ.vars "y" = j → i < n → j < n →
      ∃ bv, c.evalB B τ = some bv ∧ (bv = true ↔ P i j))
    {σ : Env} (hσ : Ctx σ) (hF : Mat σ F n fun _ _ => 0) :
    ∃ σ', Run B (flagScan F c) σ σ' (n * (n * (c.size + 50) + 14) + 6) ∧ Ctx σ' ∧
      Mat σ' F n (fun lo hi => ind (FlagP n lab P lo hi)) := by
  classical
  have hnn : n ≤ n * n := Nat.le_mul_self n
  let IX : ℕ → Env → Prop := fun k τ => Ctx τ ∧
    Mat τ F n (fun lo hi => ind (∃ x < k, ∃ y < n, x ≠ y ∧ min (lab x) (lab y) = lo ∧
      max (lab x) (lab y) = hi ∧ P x y))
  obtain ⟨σ', hr, ⟨hC, hM⟩, -⟩ :=
    forUp_run (B := B) (i := "x") (e := .var "n") (body := forUp "y" (.var "n") (flagStep F c))
      (N := n) (K := n * (c.size + 50) + 6) IX (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hCn τ hI.1]; omega), hCn τ hI.1])
      (σ := σ) ⟨hCv _ _ _ (by decide) hσ, (hF.congr fun i _ j _ => by simp [ind]).of_eq (by simp)⟩
      (by
        rintro k hk τ ⟨hC, hM⟩ hxk
        let Q : ℕ → ℕ → ℕ → Prop := fun k2 lo hi =>
          (∃ x < k, ∃ y < n, x ≠ y ∧ min (lab x) (lab y) = lo ∧ max (lab x) (lab y) = hi ∧ P x y) ∨
          (∃ y < k2, k ≠ y ∧ min (lab k) (lab y) = lo ∧ max (lab k) (lab y) = hi ∧ P k y)
        let IY : ℕ → Env → Prop := fun k2 ρ => Ctx ρ ∧ ρ.vars "x" = k ∧
          Mat ρ F n (fun lo hi => ind (Q k2 lo hi))
        obtain ⟨ρ, hrY, ⟨hCρ, hxρ, hMρ⟩, -⟩ :=
          forUp_run (B := B) (i := "y") (e := .var "n") (body := flagStep F c) (N := n)
            (K := c.size + 42) IY (by omega)
            (fun k _ τ hI _ => by rw [evalB_var (by rw [hCn τ hI.1]; omega), hCn τ hI.1])
            (σ := τ) ⟨hCv _ _ _ (by decide) hC, by simp [hxk],
              (hM.congr fun lo _ hi _ => ind_eq_iff.mpr (by simp [Q])).of_eq (by simp)⟩
            (by
              rintro k2 hk2 ρ1 ⟨hC1, hx1, hM1⟩ hy1
              have hfin : ∀ ρ2 : Env, ρ2.vars "y" = k2 → Ctx ρ2 → ρ2.vars "x" = k →
                  Mat ρ2 F n (fun lo hi => ind (Q (k2 + 1) lo hi)) →
                  IY (k2 + 1) (ρ2.setVar "y" (k2 + 1)) := fun ρ2 _ h1 h2 h3 =>
                ⟨hCv _ _ _ (by decide) h1, by simp [h2], h3.of_eq (by simp)⟩
              have hsame : ∀ lo hi, ¬ (k ≠ k2 ∧ min (lab k) (lab k2) = lo ∧
                  max (lab k) (lab k2) = hi ∧ P k k2) → (Q (k2 + 1) lo hi ↔ Q k2 lo hi) := by
                intro lo hi hno
                simp only [Q]
                constructor
                · rintro (h | ⟨y, hy, h⟩)
                  · exact Or.inl h
                  · rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | rfl
                    · exact Or.inr ⟨y, hy, h⟩
                    · exact absurd h hno
                · rintro (h | ⟨y, hy, h⟩)
                  · exact Or.inl h
                  · exact Or.inr ⟨y, by omega, h⟩
              have hxy : (Cond.eq (.var "x") (.var "y")).evalB B ρ1 = some (decide (k = k2)) := by
                rw [evalB_condEq' (evalB_var (by omega)) (evalB_var (by omega)), hx1, hy1]
              by_cases hkk : k = k2
              · refine ⟨ρ1, (Run.ite_true (by rw [hxy]; simp [hkk]) Run.skip).mono (by simp), hy1,
                  hfin ρ1 hy1 hC1 hx1 (hM1.congr fun lo _ hi _ => ind_eq_iff.mpr
                    (hsame lo hi (fun h => h.1 hkk)).symm)⟩
              have hxyf : (Cond.eq (.var "x") (.var "y")).evalB B ρ1 = some false := by
                rw [hxy]; simp [hkk]
              obtain ⟨ρ2, hr2, hlo, hhi, ha2, hi2, ho2, hv2⟩ := lohi_run (B := B) (hCc ρ1 hC1) hlab
                (by omega) hx1 hy1 hk hk2
              have hC2 : Ctx ρ2 := hCe ρ1 ρ2 hC1 ha2 hi2 ho2 hv2
              have hx2 : ρ2.vars "x" = k := by rw [hv2 "x" (by decide), hx1]
              have hy2 : ρ2.vars "y" = k2 := by rw [hv2 "y" (by decide), hy1]
              have hM2 : Mat ρ2 F n (fun lo hi => ind (Q k2 lo hi)) := hM1.of_eq (by rw [ha2])
              obtain ⟨bv, hbv, hbiff⟩ := hc ρ2 k k2 hC2 hx2 hy2 hk hk2
              by_cases hP : P k k2
              · have hbt : bv = true := hbiff.mpr hP
                subst hbt
                have hlk := hlab k hk
                have hlk2 := hlab k2 hk2
                have hlon : min (lab k) (lab k2) < n := by omega
                have hhin : max (lab k) (lab k2) < n := by omega
                have hidx := rowMajor_lt hlon hhin
                refine ⟨ρ2.setArr F (min (lab k) (lab k2) * n + max (lab k) (lab k2)) 1,
                  (Run.ite_false hxyf (Run.seq hr2 (Run.ite_true hbv (Run.store
                    (evalB_rm hlo (by rw [hCn ρ2 hC2]) hhi hhin (by omega) (by omega))
                    (evalB_lit (by omega)) (by rw [hM2.len]; exact hidx))))).mono
                    (by simp; omega), by simp [hy2],
                  hfin _ (by simp [hy2]) (hCs _ _ _ hC2) (by simp [hx2]) ⟨by simp [hM2.len],
                    fun lo hlo' hi hhi' => ?_⟩⟩
                simp only [arrs_setArr, if_true]
                rw [getElem?_set_rm hhin hhi']
                by_cases hq : lo = min (lab k) (lab k2) ∧ hi = max (lab k) (lab k2)
                · rw [if_pos hq, if_pos (by rw [hM2.len]; exact hidx)]
                  obtain ⟨rfl, rfl⟩ := hq
                  congr 1
                  exact (ind_eq_one.mpr (Or.inr ⟨k2, by omega, hkk, rfl, rfl, hP⟩)).symm
                · rw [if_neg hq, hM2.get lo hlo' hi hhi']
                  congr 1
                  refine ind_eq_iff.mpr (hsame lo hi ?_).symm
                  rintro ⟨-, h1, h2, -⟩
                  exact hq ⟨h1.symm, h2.symm⟩
              · have hbf : bv = false := by
                  cases bv
                  · rfl
                  · exact absurd (hbiff.mp rfl) hP
                subst hbf
                exact ⟨ρ2, (Run.ite_false hxyf (Run.seq hr2 (Run.ite_false hbv Run.skip))).mono
                  (by simp; omega), hy2,
                  hfin ρ2 hy2 hC2 hx2 (hM2.congr fun lo _ hi _ => ind_eq_iff.mpr
                    (hsame lo hi (fun h => hP h.2.2.2)).symm)⟩)
        refine ⟨ρ, hrY.mono (by simp), hxρ, hCv _ _ _ (by decide) hCρ, (hMρ.congr fun lo _ hi _ =>
          ind_eq_iff.mpr ?_).of_eq (by simp)⟩
        simp only [Q]
        constructor
        · rintro (⟨x, hx, h⟩ | ⟨y, hy, h⟩)
          · exact ⟨x, by omega, h⟩
          · exact ⟨k, by omega, y, hy, h⟩
        · rintro ⟨x, hx, h⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
          · exact Or.inl ⟨x, hx, h⟩
          · exact Or.inr h)
  refine ⟨σ', hr.mono (by simp), hC, hM.congr fun lo _ hi _ => ind_eq_iff.mpr ?_⟩
  simp only [FlagP]

/-- One pair of `pairSet`. -/
def pairSetStep (D : String) (c : Cond) : Com :=
  .ite (.eq (.var "x") (.var "y")) .skip
    (.seq lohi (.ite c (.store D (rm "x" "y") (.lit 1)) .skip))

/-- Set entry `(x, y)` of `D` to `1` for the pairs of distinct vertices
passing `c`, which may read the ordered labels `lo` and `hi`. -/
def pairSet (D : String) (c : Cond) : Com :=
  forUp "x" (.var "n") (forUp "y" (.var "n") (pairSetStep D c))

/-- **Setting entries of pairs.** -/
theorem pairSet_run {B n : ℕ} {D : String} {c : Cond} (Ctx : Env → Prop) (lab : ℕ → ℕ)
    (Old P : ℕ → ℕ → Prop) (hB : n * n + n + 1 < B) (hlab : ∀ z < n, lab z < n)
    (hCn : ∀ τ, Ctx τ → τ.vars "n" = n) (hCc : ∀ τ, Ctx τ → Vec τ "cur" n lab)
    (hCv : ∀ τ x v, x ∈ ["x", "y", "a", "b", "lo", "hi"] → Ctx τ → Ctx (τ.setVar x v))
    (hCe : ∀ τ τ', Ctx τ → τ'.arrs = τ.arrs → τ'.inp = τ.inp → τ'.out = τ.out →
      (∀ z, z ∉ ["a", "b", "lo", "hi"] → τ'.vars z = τ.vars z) → Ctx τ')
    (hCs : ∀ τ i v, Ctx τ → Ctx (τ.setArr D i v))
    (hc : ∀ τ i j, Ctx τ → τ.vars "x" = i → τ.vars "y" = j → i < n → j < n →
      τ.vars "lo" = min (lab i) (lab j) → τ.vars "hi" = max (lab i) (lab j) →
      ∃ bv, c.evalB B τ = some bv ∧ (bv = true ↔ P i j))
    {σ : Env} (hσ : Ctx σ) (hD : Mat σ D n fun x y => ind (Old x y)) :
    ∃ σ', Run B (pairSet D c) σ σ' (n * (n * (c.size + 50) + 14) + 6) ∧ Ctx σ' ∧
      Mat σ' D n (fun x y => ind (Old x y ∨ (x ≠ y ∧ P x y))) := by
  classical
  have hnn : n ≤ n * n := Nat.le_mul_self n
  let IX : ℕ → Env → Prop := fun k τ => Ctx τ ∧
    Mat τ D n (fun x y => ind (Old x y ∨ (x < k ∧ x ≠ y ∧ P x y)))
  obtain ⟨σ', hr, ⟨hC, hM⟩, -⟩ :=
    forUp_run (B := B) (i := "x") (e := .var "n") (body := forUp "y" (.var "n") (pairSetStep D c))
      (N := n) (K := n * (c.size + 50) + 6) IX (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hCn τ hI.1]; omega), hCn τ hI.1])
      (σ := σ) ⟨hCv _ _ _ (by decide) hσ, (hD.congr fun i _ j _ => by simp).of_eq (by simp)⟩
      (by
        rintro k hk τ ⟨hC, hM⟩ hxk
        let Q : ℕ → ℕ → ℕ → Prop := fun k2 x y =>
          Old x y ∨ (x < k ∧ x ≠ y ∧ P x y) ∨ (x = k ∧ y < k2 ∧ x ≠ y ∧ P x y)
        let IY : ℕ → Env → Prop := fun k2 ρ => Ctx ρ ∧ ρ.vars "x" = k ∧
          Mat ρ D n (fun x y => ind (Q k2 x y))
        obtain ⟨ρ, hrY, ⟨hCρ, hxρ, hMρ⟩, -⟩ :=
          forUp_run (B := B) (i := "y") (e := .var "n") (body := pairSetStep D c) (N := n)
            (K := c.size + 42) IY (by omega)
            (fun k _ τ hI _ => by rw [evalB_var (by rw [hCn τ hI.1]; omega), hCn τ hI.1])
            (σ := τ) ⟨hCv _ _ _ (by decide) hC, by simp [hxk],
              (hM.congr fun x _ y _ => ind_eq_iff.mpr (by simp [Q])).of_eq (by simp)⟩
            (by
              rintro k2 hk2 ρ1 ⟨hC1, hx1, hM1⟩ hy1
              have hfin : ∀ ρ2 : Env, ρ2.vars "y" = k2 → Ctx ρ2 → ρ2.vars "x" = k →
                  Mat ρ2 D n (fun x y => ind (Q (k2 + 1) x y)) →
                  IY (k2 + 1) (ρ2.setVar "y" (k2 + 1)) := fun ρ2 _ h1 h2 h3 =>
                ⟨hCv _ _ _ (by decide) h1, by simp [h2], h3.of_eq (by simp)⟩
              have hsame : ∀ x y, ¬ (x = k ∧ y = k2 ∧ x ≠ y ∧ P x y) →
                  (Q (k2 + 1) x y ↔ Q k2 x y) := by
                intro x y hno
                simp only [Q]
                constructor
                · rintro (h | h | ⟨h1, h2, h3, h4⟩)
                  · exact Or.inl h
                  · exact Or.inr (Or.inl h)
                  · rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h2 | rfl
                    · exact Or.inr (Or.inr ⟨h1, h2, h3, h4⟩)
                    · exact absurd ⟨h1, rfl, h3, h4⟩ hno
                · rintro (h | h | ⟨h1, h2, h3, h4⟩)
                  · exact Or.inl h
                  · exact Or.inr (Or.inl h)
                  · exact Or.inr (Or.inr ⟨h1, by omega, h3, h4⟩)
              have hxy : (Cond.eq (.var "x") (.var "y")).evalB B ρ1 = some (decide (k = k2)) := by
                rw [evalB_condEq' (evalB_var (by omega)) (evalB_var (by omega)), hx1, hy1]
              by_cases hkk : k = k2
              · refine ⟨ρ1, (Run.ite_true (by rw [hxy]; simp [hkk]) Run.skip).mono (by simp), hy1,
                  hfin ρ1 hy1 hC1 hx1 (hM1.congr fun x _ y _ => ind_eq_iff.mpr
                    (hsame x y (fun h => h.2.2.1 (h.1.trans (hkk.trans h.2.1.symm)))).symm)⟩
              have hxyf : (Cond.eq (.var "x") (.var "y")).evalB B ρ1 = some false := by
                rw [hxy]; simp [hkk]
              obtain ⟨ρ2, hr2, hlo, hhi, ha2, hi2, ho2, hv2⟩ := lohi_run (B := B) (hCc ρ1 hC1) hlab
                (by omega) hx1 hy1 hk hk2
              have hC2 : Ctx ρ2 := hCe ρ1 ρ2 hC1 ha2 hi2 ho2 hv2
              have hx2 : ρ2.vars "x" = k := by rw [hv2 "x" (by decide), hx1]
              have hy2 : ρ2.vars "y" = k2 := by rw [hv2 "y" (by decide), hy1]
              have hM2 : Mat ρ2 D n (fun x y => ind (Q k2 x y)) := hM1.of_eq (by rw [ha2])
              obtain ⟨bv, hbv, hbiff⟩ := hc ρ2 k k2 hC2 hx2 hy2 hk hk2 hlo hhi
              by_cases hP : P k k2
              · have hbt : bv = true := hbiff.mpr hP
                subst hbt
                have hidx := rowMajor_lt hk hk2
                refine ⟨ρ2.setArr D (k * n + k2) 1,
                  (Run.ite_false hxyf (Run.seq hr2 (Run.ite_true hbv (Run.store
                    (evalB_rm hx2 (by rw [hCn ρ2 hC2]) hy2 hk2 (by omega) (by omega))
                    (evalB_lit (by omega)) (by rw [hM2.len]; exact hidx))))).mono
                    (by simp; omega), by simp [hy2],
                  hfin _ (by simp [hy2]) (hCs _ _ _ hC2) (by simp [hx2]) ⟨by simp [hM2.len],
                    fun x hx y hy => ?_⟩⟩
                simp only [arrs_setArr, if_true]
                rw [getElem?_set_rm hk2 hy]
                by_cases hq : x = k ∧ y = k2
                · rw [if_pos hq, if_pos (by rw [hM2.len]; exact hidx)]
                  obtain ⟨rfl, rfl⟩ := hq
                  congr 1
                  exact (ind_eq_one.mpr (Or.inr (Or.inr ⟨rfl, by omega, hkk, hP⟩))).symm
                · rw [if_neg hq, hM2.get x hx y hy]
                  congr 1
                  refine ind_eq_iff.mpr (hsame x y ?_).symm
                  rintro ⟨h1, h2, -⟩
                  exact hq ⟨h1, h2⟩
              · have hbf : bv = false := by
                  cases bv
                  · rfl
                  · exact absurd (hbiff.mp rfl) hP
                subst hbf
                exact ⟨ρ2, (Run.ite_false hxyf (Run.seq hr2 (Run.ite_false hbv Run.skip))).mono
                  (by simp; omega), hy2,
                  hfin ρ2 hy2 hC2 hx2 (hM2.congr fun x _ y _ => ind_eq_iff.mpr
                    (hsame x y (fun h => hP (h.1 ▸ h.2.1 ▸ h.2.2.2))).symm)⟩)
        refine ⟨ρ, hrY.mono (by simp), hxρ, hCv _ _ _ (by decide) hCρ, (hMρ.congr fun x _ y hy =>
          ind_eq_iff.mpr ?_).of_eq (by simp)⟩
        simp only [Q]
        constructor
        · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
          · exact Or.inl h
          · exact Or.inr ⟨by omega, h2⟩
          · exact Or.inr ⟨by omega, h3⟩
        · rintro (h | ⟨h1, h2⟩)
          · exact Or.inl h
          · rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | rfl
            · exact Or.inr (Or.inl ⟨h1, h2⟩)
            · exact Or.inr (Or.inr ⟨rfl, hy, h2⟩))
  refine ⟨σ', hr.mono (by simp), hC, hM.congr fun x hx y _ => ind_eq_iff.mpr ?_⟩
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩

end Lax185574Proofs.Conversions.Ram
