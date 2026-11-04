import Lax185574Proofs.Words.ForLoop

/-!
Small helpers for the programs of the conversions: row-major indices,
their bounded evaluation, and reading matrix entries.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- The row-major index `x · n + y` of the scalars `x` and `y`. -/
def rm (x y : String) : Expr := .add (.mul (.var x) (.var "n")) (.var y)

@[simp] theorem size_rm (x y : String) : (rm x y).size = 5 := rfl

theorem evalB_rm {B : ℕ} {σ : Env} {x y : String} {i n j : ℕ} (hx : σ.vars x = i)
    (hn : σ.vars "n" = n) (hy : σ.vars y = j) (hj : j < n) (hnB : n < B) (h : i * n + j < B) :
    (rm x y).evalB B σ = some (i * n + j) := by
  have hi : i ≤ i * n := Nat.le_mul_of_pos_right _ (by omega)
  have := evalB_bin (op := .add) (evalB_bin (op := .mul) (evalB_var (B := B) (x := x) (σ := σ)
    (by omega)) (evalB_var (x := "n") (by omega)) (by simp [hx, hn]; omega))
    (evalB_var (x := y) (by omega)) (by simp [hx, hn, hy]; omega)
  simpa [rm, hx, hn, hy] using this

theorem evalB_getRM {B : ℕ} {σ : Env} {a x y : String} {i n j w : ℕ} (hx : σ.vars x = i)
    (hn : σ.vars "n" = n) (hy : σ.vars y = j) (hj : j < n) (hnB : n < B) (h : i * n + j < B)
    (hget : (σ.arrs a)[i * n + j]? = some w) (hw : w < B) :
    (Expr.get a (rm x y)).evalB B σ = some w :=
  evalB_get (evalB_rm hx hn hy hj hnB h) hget hw

theorem evalB_getVar {B : ℕ} {σ : Env} {a x : String} {i w : ℕ} (hx : σ.vars x = i) (hi : i < B)
    (hget : (σ.arrs a)[i]? = some w) (hw : w < B) :
    (Expr.get a (.var x)).evalB B σ = some w :=
  evalB_get (by rw [evalB_var (by omega), hx]) hget hw

theorem eq_lit_evalB {B : ℕ} {σ : Env} {x : String} {n : ℕ} (hx : σ.vars x < B) (hn : n < B) :
    (Cond.eq (.var x) (.lit n)).evalB B σ = some (decide (σ.vars x = n)) := by
  rw [evalB_condEq (evalB_var hx) (evalB_lit hn)]
  by_cases h : σ.vars x = n <;> simp [h]

theorem evalB_condEq' {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ}
    (he : e.evalB B σ = some m) (hf : f.evalB B σ = some n) :
    (Cond.eq e f).evalB B σ = some (decide (m = n)) := by
  rw [evalB_condEq he hf]
  by_cases h : m = n <;> simp [h]

/-- The `0`/`1` value of a proposition. -/
noncomputable def ind (p : Prop) : ℕ := open Classical in if p then 1 else 0

theorem ind_le_one (p : Prop) : ind p ≤ 1 := by
  unfold ind; split <;> omega

theorem ind_eq_one {p : Prop} : ind p = 1 ↔ p := by
  unfold ind; split <;> simp_all

theorem ind_eq_iff {p q : Prop} : ind p = ind q ↔ (p ↔ q) := by
  unfold ind
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

/-- The array `arr` has length `n` and entry `i` is `f i`. -/
structure Vec (τ : Env) (arr : String) (n : ℕ) (f : ℕ → ℕ) : Prop where
  len : (τ.arrs arr).length = n
  get : ∀ i < n, (τ.arrs arr)[i]? = some (f i)

/-- The array `arr` is an `n × n` matrix in row-major order, with entry
`(i, j)` equal to `f i j`. -/
structure Mat (τ : Env) (arr : String) (n : ℕ) (f : ℕ → ℕ → ℕ) : Prop where
  len : (τ.arrs arr).length = n * n
  get : ∀ i < n, ∀ j < n, (τ.arrs arr)[i * n + j]? = some (f i j)

theorem Vec.of_eq {τ τ' : Env} {arr : String} {n : ℕ} {f : ℕ → ℕ} (h : Vec τ arr n f)
    (he : τ'.arrs arr = τ.arrs arr) : Vec τ' arr n f := ⟨by rw [he, h.len], by rw [he]; exact h.get⟩

theorem Mat.of_eq {τ τ' : Env} {arr : String} {n : ℕ} {f : ℕ → ℕ → ℕ} (h : Mat τ arr n f)
    (he : τ'.arrs arr = τ.arrs arr) : Mat τ' arr n f := ⟨by rw [he, h.len], by rw [he]; exact h.get⟩

theorem Vec.congr {τ : Env} {arr : String} {n : ℕ} {f g : ℕ → ℕ} (h : Vec τ arr n f)
    (hfg : ∀ i < n, f i = g i) : Vec τ arr n g :=
  ⟨h.len, fun i hi => by rw [h.get i hi, hfg i hi]⟩

theorem Mat.congr {τ : Env} {arr : String} {n : ℕ} {f g : ℕ → ℕ → ℕ} (h : Mat τ arr n f)
    (hfg : ∀ i < n, ∀ j < n, f i j = g i j) : Mat τ arr n g :=
  ⟨h.len, fun i hi j hj => by rw [h.get i hi j hj, hfg i hi j hj]⟩

/-- Evaluating a matrix entry. -/
theorem Mat.evalB {B : ℕ} {τ : Env} {arr x y : String} {n i j : ℕ} {f : ℕ → ℕ → ℕ}
    (h : Mat τ arr n f) (hn : τ.vars "n" = n) (hx : τ.vars x = i) (hy : τ.vars y = j)
    (hi : i < n) (hj : j < n) (hB : n * n < B) (hnB : n < B) (hf : f i j < B) :
    (Expr.get arr (rm x y)).evalB B τ = some (f i j) :=
  evalB_getRM hx hn hy hj hnB (by have := rowMajor_lt hi hj; omega) (h.get i hi j hj) hf

/-- Evaluating a vector entry. -/
theorem Vec.evalB {B : ℕ} {τ : Env} {arr x : String} {n i : ℕ} {f : ℕ → ℕ}
    (h : Vec τ arr n f) (hx : τ.vars x = i) (hi : i < n) (hnB : n < B) (hf : f i < B) :
    (Expr.get arr (.var x)).evalB B τ = some (f i) :=
  evalB_getVar hx (by omega) (h.get i hi) hf

/-- Fill entries `base, …, base + n - 1` of `arr` with the values of `e`
for `b = 0, …, n - 1`. -/
def rowFill (arr : String) (ie e : Expr) : Com := forUp "b" (.var "n") (.store arr ie e)

/-- **Filling a row.** `Ctx` must survive setting `b` and storing into
`arr`. -/
theorem rowFill_run {B n base K : ℕ} {arr : String} {ie e : Expr} (Ctx : Env → Prop)
    (f : ℕ → ℕ) (hnB : n < B)
    (hCn : ∀ τ, Ctx τ → τ.vars "n" = n)
    (hCb : ∀ τ x, Ctx τ → Ctx (τ.setVar "b" x)) (hCa : ∀ τ i x, Ctx τ → Ctx (τ.setArr arr i x))
    (hie : ∀ τ k, Ctx τ → τ.vars "b" = k → k < n → ie.evalB B τ = some (base + k))
    (he : ∀ τ k, Ctx τ → τ.vars "b" = k → k < n → e.evalB B τ = some (f k))
    (hsz : 1 + ie.size + e.size ≤ K)
    {σ : Env} (hσ : Ctx σ) (hlen : base + n ≤ (σ.arrs arr).length) :
    ∃ σ', Run B (rowFill arr ie e) σ σ' (n * (K + 8) + 6) ∧ Ctx σ' ∧
      (σ'.arrs arr).length = (σ.arrs arr).length ∧
      ∀ j, (σ'.arrs arr)[j]? =
        if base ≤ j ∧ j < base + n then some (f (j - base)) else (σ.arrs arr)[j]? := by
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ (τ.arrs arr).length = (σ.arrs arr).length ∧
    ∀ j, (τ.arrs arr)[j]? = if base ≤ j ∧ j < base + k then some (f (j - base)) else (σ.arrs arr)[j]?
  obtain ⟨σ', hr, ⟨hC, hl, hg⟩, -⟩ :=
    forUp_run (B := B) (i := "b") (e := .var "n") (body := .store arr ie e) (N := n) (K := K) I
      hnB (fun k _ τ hI _ => by rw [evalB_var (by rw [hCn τ hI.1]; omega), hCn τ hI.1])
      (σ := σ) ⟨hCb _ _ hσ, by simp, fun j => by simp⟩
      (by
        rintro k hk τ ⟨hC, hl, hg⟩ hbk
        refine ⟨_, (Run.store (hie τ k hC hbk hk) (he τ k hC hbk hk) (by omega)).mono hsz,
          by simp [hbk], hCb _ _ (hCa _ _ _ hC), by simp [hl], fun j => ?_⟩
        simp only [arrs_setVar, arrs_setArr, if_true, List.getElem?_set, hg j]
        by_cases hj : base + k = j
        · subst hj; simp [hl]; omega
        · simp only [hj, if_false]
          have : (base ≤ j ∧ j < base + (k + 1)) ↔ (base ≤ j ∧ j < base + k) := by omega
          simp only [this])
  exact ⟨σ', hr.mono (by simp), hC, hl, hg⟩

/-- Fill the `n × n` matrix `arr` with the values of `e` at `(a, b)`. -/
def matFill (arr : String) (e : Expr) : Com := forUp "a" (.var "n") (rowFill arr (rm "a" "b") e)

/-- **Filling a matrix.** -/
theorem matFill_run {B n K : ℕ} {arr : String} {e : Expr} (Ctx : Env → Prop)
    (f : ℕ → ℕ → ℕ) (hB : n * n + n + 1 < B)
    (hCn : ∀ τ, Ctx τ → τ.vars "n" = n)
    (hCa : ∀ τ x, Ctx τ → Ctx (τ.setVar "a" x)) (hCb : ∀ τ x, Ctx τ → Ctx (τ.setVar "b" x))
    (hCs : ∀ τ i x, Ctx τ → Ctx (τ.setArr arr i x))
    (he : ∀ τ i j, Ctx τ → τ.vars "a" = i → τ.vars "b" = j → i < n → j < n →
      e.evalB B τ = some (f i j))
    (hsz : 6 + e.size ≤ K)
    {σ : Env} (hσ : Ctx σ) (hlen : (σ.arrs arr).length = n * n) :
    ∃ σ', Run B (matFill arr e) σ σ' (n * (n * (K + 8) + 14) + 6) ∧ Ctx σ' ∧ Mat σ' arr n f := by
  have hnn : n ≤ n * n := Nat.le_mul_self n
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ (τ.arrs arr).length = n * n ∧
    ∀ i < k, ∀ j < n, (τ.arrs arr)[i * n + j]? = some (f i j)
  obtain ⟨σ', hr, ⟨hC, hl, hg⟩, -⟩ :=
    forUp_run (B := B) (i := "a") (e := .var "n") (body := rowFill arr (rm "a" "b") e) (N := n)
      (K := n * (K + 8) + 6) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hCn τ hI.1]; omega), hCn τ hI.1])
      (σ := σ) ⟨hCa _ _ hσ, by simp [hlen], fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      (by
        rintro k hk τ ⟨hC, hl, hg⟩ hak
        have hkn : k * n + n ≤ n * n := by
          have := Nat.mul_le_mul_right n (show k + 1 ≤ n by omega)
          rw [Nat.add_mul] at this; omega
        obtain ⟨τ', hr', ⟨hC', ha'⟩, hl', hg'⟩ := rowFill_run (B := B) (base := k * n) (K := K)
          (arr := arr) (ie := rm "a" "b") (e := e) (fun ρ => Ctx ρ ∧ ρ.vars "a" = k) (f k)
          (by omega) (fun ρ h => hCn ρ h.1) (fun ρ x h => ⟨hCb _ _ h.1, by simp [h.2]⟩)
          (fun ρ i x h => ⟨hCs _ _ _ h.1, by simp [h.2]⟩)
          (fun ρ j h hb hj => evalB_rm h.2 (hCn ρ h.1) hb hj (by omega) (by omega))
          (fun ρ j h hb hj => he ρ k j h.1 h.2 hb hk hj)
          (by simp; omega) ⟨hC, hak⟩ (by omega)
        refine ⟨τ', hr', ha', hCa _ _ hC', by simp [hl', hl], fun i hi j hj => ?_⟩
        simp only [arrs_setVar]
        rw [hg' (i * n + j)]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · have : i * n + j < k * n := by
            have := Nat.mul_le_mul_right n (show i + 1 ≤ k by omega)
            rw [Nat.add_mul] at this; omega
          rw [if_neg (by omega)]
          exact hg i hi j hj
        · rw [if_pos ⟨by omega, by omega⟩]
          simp)
  exact ⟨σ', hr.mono (by simp), hC, ⟨hl, hg⟩⟩

/-- `1` if the scalars `x` and `y` are equal, else `0`. -/
def eqE (x y : String) : Expr :=
  .sub (.sub (.lit 1) (.sub (.var x) (.var y))) (.sub (.var y) (.var x))

@[simp] theorem size_eqE (x y : String) : (eqE x y).size = 9 := rfl

theorem evalB_eqE {B : ℕ} {σ : Env} {x y : String} (hx : σ.vars x < B) (hy : σ.vars y < B)
    (hB : 1 < B) : (eqE x y).evalB B σ = some (ind (σ.vars x = σ.vars y)) := by
  have h1 := evalB_bin (op := .sub) (evalB_var (x := x) hx) (evalB_var (x := y) hy)
    (by simp; omega)
  have h2 := evalB_bin (op := .sub) (evalB_var (x := y) hy) (evalB_var (x := x) hx)
    (by simp; omega)
  have h3 := evalB_bin (op := .sub) (evalB_lit (n := 1) (σ := σ) hB) h1 (by simp; omega)
  have h4 := evalB_bin (op := .sub) h3 h2 (by simp; omega)
  unfold eqE
  simp only [Expr.sub_def]
  rw [h4]
  unfold ind
  by_cases h : σ.vars x = σ.vars y
  · simp [h]
  · simp [h]; omega

theorem land_ind (p q : Prop) : Nat.land (ind p) (ind q) = ind (p ∧ q) := by
  unfold ind
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem lor_ind (p q : Prop) : Nat.lor (ind p) (ind q) = ind (p ∨ q) := by
  unfold ind
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem one_sub_ind (p : Prop) : 1 - ind p = ind (¬ p) := by
  unfold ind
  by_cases hp : p <;> simp [hp]

theorem land_le_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : Nat.land a b ≤ 1 := by
  interval_cases a <;> interval_cases b <;> decide

theorem lor_le_one {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) : Nat.lor a b ≤ 1 := by
  interval_cases a <;> interval_cases b <;> decide

end Lax185574Proofs.Conversions.Ram
