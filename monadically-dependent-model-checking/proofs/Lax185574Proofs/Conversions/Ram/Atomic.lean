import Lax185574Proofs.Conversions.Ram.Classify

/-!
The equivalence tests of the partition into atomic types and of its
split along the least vertices of the parts.

The graph is held as an adjacency matrix `adj` of width `n`, the vertex
set `X` as row `t` of the matrix `inS`, and the labels of the atomic
types as the array `lab`. Both tests leave `1` or `0` in `ok`.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- Atomic types over `X`: equal, or both outside `X` with the same
neighbors in `X`. -/
def RAtom (n : ℕ) (X : ℕ → Prop) (A : ℕ → ℕ → Prop) (u v : ℕ) : Prop :=
  u = v ∨ (¬ X u ∧ ¬ X v ∧ ∀ z < n, X z → (A u z ↔ A v z))

/-- One round of the scan over `z` of `eqA`. -/
def zstepA : Com :=
  .ite (.eq (.get "inS" (rm "t" "z")) (.lit 1))
    (.ite (.eq (.get "adj" (rm "u" "z")) (.get "adj" (rm "v" "z"))) .skip (.assign "ok" (.lit 0)))
    .skip

/-- The test of `RAtom`. -/
def eqA : Com :=
  .seq (.assign "ok" (.lit 1))
    (.ite (.eq (.var "u") (.var "v")) .skip
      (.ite (.eq (.get "inS" (rm "t" "u")) (.lit 1)) (.assign "ok" (.lit 0))
        (.ite (.eq (.get "inS" (rm "t" "v")) (.lit 1)) (.assign "ok" (.lit 0))
          (forUp "z" (.var "n") zstepA))))

/-- What the tests read: the sizes, the set `X` and the graph. -/
structure MatCtx (n t : ℕ) (X : ℕ → Prop) (A : ℕ → ℕ → Prop) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  ht : τ.vars "t" = t
  hinS : ∀ z < n, (τ.arrs "inS")[t * n + z]? = some (ind (X z))
  hadj : ∀ u < n, ∀ z < n, (τ.arrs "adj")[u * n + z]? = some (ind (A u z))

theorem MatCtx.of_eq {n t : ℕ} {X : ℕ → Prop} {A : ℕ → ℕ → Prop} {τ τ' : Env}
    (h : MatCtx n t X A τ) (hn : τ'.vars "n" = τ.vars "n") (ht : τ'.vars "t" = τ.vars "t")
    (hi : τ'.arrs "inS" = τ.arrs "inS") (ha : τ'.arrs "adj" = τ.arrs "adj") :
    MatCtx n t X A τ' :=
  ⟨by rw [hn, h.hn], by rw [ht, h.ht], by rw [hi]; exact h.hinS, by rw [ha]; exact h.hadj⟩

theorem idx_lt_sq {n i j : ℕ} (hi : i < n) (hj : j < n) : i * n + j < n * n := rowMajor_lt hi hj

theorem eqA_run {B n t : ℕ} {X : ℕ → Prop} {A : ℕ → ℕ → Prop} {τ : Env}
    (hc : MatCtx n t X A τ) (hu : τ.vars "u" < n) (hv : τ.vars "v" < n)
    (hB1 : t * n + n < B) (hB2 : n * n < B) (hnB : n + 1 < B) :
    ∃ τ', Run B eqA τ τ' (40 * n + 40) ∧
      τ'.vars "ok" = ind (RAtom n X A (τ.vars "u") (τ.vars "v")) := by
  classical
  set u := τ.vars "u" with hu'
  set v := τ.vars "v" with hv'
  set τ1 := τ.setVar "ok" 1 with hτ1
  have hc1 : MatCtx n t X A τ1 := hc.of_eq (by simp [hτ1]) (by simp [hτ1]) rfl rfl
  have h1 : Run B (.assign "ok" (.lit 1)) τ τ1 2 := Run.assign (by simp; omega)
  have hrow : ∀ ρ : Env, MatCtx n t X A ρ → ∀ x : String, ∀ w < n, ρ.vars x = w →
      (Expr.get "inS" (rm "t" x)).evalB B ρ = some (ind (X w)) := by
    intro ρ hρ x w hw hx
    exact evalB_getRM hρ.ht hρ.hn hx hw (by omega) (by omega) (hρ.hinS w hw) (by
      have := ind_le_one (X w); omega)
  have hadj : ∀ ρ : Env, MatCtx n t X A ρ → ∀ x : String, ∀ i < n, ρ.vars x = i →
      ∀ w < n, ρ.vars "z" = w →
      (Expr.get "adj" (rm x "z")).evalB B ρ = some (ind (A i w)) := by
    intro ρ hρ x i hi hx w hw hz
    have := idx_lt_sq hi hw
    exact evalB_getRM hx hρ.hn hz hw (by omega) (by omega) (hρ.hadj i hi w hw) (by
      have := ind_le_one (A i w); omega)
  by_cases huv : u = v
  · refine ⟨τ1, (Run.seq h1 (Run.ite_true ?_ Run.skip)).mono (by simp), ?_⟩
    · rw [evalB_condEq' (evalB_var (by simp [hτ1]; omega)) (evalB_var (by simp [hτ1]; omega))]
      simp [hτ1, ← hu', ← hv', huv]
    · simp [hτ1, ind, RAtom, huv]
  have hne : (Cond.eq (.var "u") (.var "v")).evalB B τ1 = some false := by
    rw [evalB_condEq' (evalB_var (by simp [hτ1]; omega)) (evalB_var (by simp [hτ1]; omega))]
    simp [hτ1, ← hu', ← hv', huv]
  by_cases hXu : X u
  · refine ⟨τ1.setVar "ok" 0, (Run.seq h1 (Run.ite_false hne (Run.ite_true ?_
      (Run.assign (v := 0) (by simp; omega))))).mono (by simp), ?_⟩
    · rw [evalB_condEq' (hrow τ1 hc1 "u" u hu (by simp [hτ1, hu'])) (evalB_lit (by omega))]
      simp [ind, hXu]
    · simp [ind, RAtom, huv, hXu]
  have hXu' : (Cond.eq (.get "inS" (rm "t" "u")) (.lit 1)).evalB B τ1 = some false := by
    rw [evalB_condEq' (hrow τ1 hc1 "u" u hu (by simp [hτ1, hu'])) (evalB_lit (by omega))]
    simp [ind, hXu]
  by_cases hXv : X v
  · refine ⟨τ1.setVar "ok" 0, (Run.seq h1 (Run.ite_false hne (Run.ite_false hXu' (Run.ite_true ?_
      (Run.assign (v := 0) (by simp; omega)))))).mono (by simp), ?_⟩
    · rw [evalB_condEq' (hrow τ1 hc1 "v" v hv (by simp [hτ1, hv'])) (evalB_lit (by omega))]
      simp [ind, hXv]
    · simp [ind, RAtom, huv, hXv]
  have hXv' : (Cond.eq (.get "inS" (rm "t" "v")) (.lit 1)).evalB B τ1 = some false := by
    rw [evalB_condEq' (hrow τ1 hc1 "v" v hv (by simp [hτ1, hv'])) (evalB_lit (by omega))]
    simp [ind, hXv]
  -- the scan over z
  let Z : ℕ → Env → Prop := fun k ρ => MatCtx n t X A ρ ∧ ρ.vars "u" = u ∧ ρ.vars "v" = v ∧
    ρ.vars "ok" = ind (∀ z < k, X z → (A u z ↔ A v z))
  obtain ⟨ρ, hrz, ⟨-, -, -, hokρ⟩, -⟩ :=
    forUp_run (B := B) (i := "z") (e := .var "n") (body := zstepA) (N := n) (K := 30) Z
      (by omega) (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
      (σ := τ1) ⟨hc1.of_eq (by simp) (by simp) rfl rfl, by simp [hτ1, hu'], by simp [hτ1, hv'],
        by simp [hτ1, ind]⟩
      (by
        rintro k hk ρ ⟨hcρ, huρ, hvρ, hokρ⟩ hzk
        have hxz := hrow ρ hcρ "z" k hk hzk
        have hau := hadj ρ hcρ "u" u hu huρ k hk hzk
        have hav := hadj ρ hcρ "v" v hv hvρ k hk hzk
        have hsucc : (∀ z < k + 1, X z → (A u z ↔ A v z)) ↔
            ((∀ z < k, X z → (A u z ↔ A v z)) ∧ (X k → (A u k ↔ A v k))) := by
          constructor
          · intro h; exact ⟨fun z hz => h z (by omega), h k (by omega)⟩
          · rintro ⟨h1, h2⟩ z hz
            rcases Nat.lt_succ_iff_lt_or_eq.mp hz with hz | rfl
            · exact h1 z hz
            · exact h2
        have hfin : ∀ ρ' : Env, ρ'.vars "z" = k → MatCtx n t X A ρ' → ρ'.vars "u" = u →
            ρ'.vars "v" = v → ρ'.vars "ok" = ind (∀ z < k + 1, X z → (A u z ↔ A v z)) →
            Z (k + 1) (ρ'.setVar "z" (k + 1)) := fun ρ' _ h1 h2 h3 h4 =>
          ⟨h1.of_eq (by simp) (by simp) rfl rfl, by simp [h2], by simp [h3], by simp [h4]⟩
        by_cases hXk : X k
        · have hc' : (Cond.eq (.get "inS" (rm "t" "z")) (.lit 1)).evalB B ρ = some true := by
            rw [evalB_condEq' hxz (evalB_lit (by omega))]; simp [ind, hXk]
          by_cases hA : (A u k ↔ A v k)
          · refine ⟨ρ, (Run.ite_true hc' (Run.ite_true ?_ Run.skip)).mono (by simp), hzk,
              hfin ρ hzk hcρ huρ hvρ ?_⟩
            · rw [evalB_condEq' hau hav]; simp [ind_eq_iff.mpr hA]
            · rw [hokρ]; exact ind_eq_iff.mpr (by rw [hsucc]; exact ⟨fun h => ⟨h, fun _ => hA⟩, And.left⟩)
          · refine ⟨ρ.setVar "ok" 0, (Run.ite_true hc' (Run.ite_false ?_
              (Run.assign (v := 0) (by simp; omega)))).mono (by simp), by simp [hzk],
              hfin _ (by simp [hzk]) (hcρ.of_eq (by simp) (by simp) rfl rfl) (by simp [huρ])
                (by simp [hvρ]) ?_⟩
            · rw [evalB_condEq' hau hav]
              simp only [Option.some.injEq, decide_eq_false_iff_not]
              exact fun h => hA (ind_eq_iff.mp h)
            · simp only [vars_setVar, if_true]
              have : ¬ (∀ z < k + 1, X z → (A u z ↔ A v z)) := fun h => hA (h k (by omega) hXk)
              simp only [ind]; rw [if_neg this]
        · have hc' : (Cond.eq (.get "inS" (rm "t" "z")) (.lit 1)).evalB B ρ = some false := by
            rw [evalB_condEq' hxz (evalB_lit (by omega))]; simp [ind, hXk]
          refine ⟨ρ, (Run.ite_false hc' Run.skip).mono (by simp), hzk,
            hfin ρ hzk hcρ huρ hvρ ?_⟩
          rw [hokρ]
          exact ind_eq_iff.mpr (by rw [hsucc]; exact ⟨fun h => ⟨h, fun hx => absurd hx hXk⟩, And.left⟩))
  refine ⟨ρ, (Run.seq h1 (Run.ite_false hne (Run.ite_false hXu' (Run.ite_false hXv' hrz)))).mono
    (by simp; omega), ?_⟩
  rw [hokρ]
  exact ind_eq_iff.mpr (by simp [RAtom, huv, hXu, hXv])

/-- The split of the partition with labels `L` along its least vertices:
the same label, and the same neighbors among the least vertices of the
other parts. -/
def RSplit (n : ℕ) (L : ℕ → ℕ) (A : ℕ → ℕ → Prop) (u v : ℕ) : Prop :=
  L u = L v ∧ ∀ z < n, L z = z → L z ≠ L u → (A u z ↔ A v z)

/-- One round of the scan over `z` of `eqQ`. -/
def zstepQ : Com :=
  .ite (.eq (.get "lab" (.var "z")) (.var "z"))
    (.ite (.eq (.get "lab" (.var "z")) (.get "lab" (.var "u"))) .skip
      (.ite (.eq (.get "adj" (rm "u" "z")) (.get "adj" (rm "v" "z"))) .skip
        (.assign "ok" (.lit 0))))
    .skip

/-- The test of `RSplit`. -/
def eqQ : Com :=
  .seq (.assign "ok" (.lit 1))
    (.ite (.eq (.get "lab" (.var "u")) (.get "lab" (.var "v")))
      (forUp "z" (.var "n") zstepQ)
      (.assign "ok" (.lit 0)))

/-- The labels `L` are in the array `lab`. -/
def LabAt (n : ℕ) (L : ℕ → ℕ) (τ : Env) : Prop := ∀ z < n, (τ.arrs "lab")[z]? = some (L z)

theorem eqQ_run {B n t : ℕ} {X : ℕ → Prop} {A : ℕ → ℕ → Prop} {L : ℕ → ℕ} {τ : Env}
    (hc : MatCtx n t X A τ) (hl : LabAt n L τ) (hL : ∀ z < n, L z ≤ n)
    (hu : τ.vars "u" < n) (hv : τ.vars "v" < n) (hB2 : n * n < B) (hnB : n + 1 < B) :
    ∃ τ', Run B eqQ τ τ' (50 * n + 40) ∧
      τ'.vars "ok" = ind (RSplit n L A (τ.vars "u") (τ.vars "v")) := by
  classical
  set u := τ.vars "u" with hu'
  set v := τ.vars "v" with hv'
  set τ1 := τ.setVar "ok" 1 with hτ1
  have hc1 : MatCtx n t X A τ1 := hc.of_eq (by simp [hτ1]) (by simp [hτ1]) rfl rfl
  have h1 : Run B (.assign "ok" (.lit 1)) τ τ1 2 := Run.assign (by simp; omega)
  have hlab : ∀ ρ : Env, LabAt n L ρ → ∀ x : String, ∀ w < n, ρ.vars x = w →
      (Expr.get "lab" (.var x)).evalB B ρ = some (L w) := by
    intro ρ hρ x w hw hx
    exact evalB_getVar hx (by omega) (hρ w hw) (by have := hL w hw; omega)
  have hadj : ∀ ρ : Env, MatCtx n t X A ρ → ∀ x : String, ∀ i < n, ρ.vars x = i →
      ∀ w < n, ρ.vars "z" = w →
      (Expr.get "adj" (rm x "z")).evalB B ρ = some (ind (A i w)) := by
    intro ρ hρ x i hi hx w hw hz
    have := idx_lt_sq hi hw
    exact evalB_getRM hx hρ.hn hz hw (by omega) (by omega) (hρ.hadj i hi w hw) (by
      have := ind_le_one (A i w); omega)
  have hl1 : LabAt n L τ1 := by simpa [LabAt, hτ1] using hl
  by_cases hLuv : L u = L v
  swap
  · refine ⟨τ1.setVar "ok" 0, (Run.seq h1 (Run.ite_false ?_
      (Run.assign (v := 0) (by simp; omega)))).mono (by simp), ?_⟩
    · rw [evalB_condEq' (hlab τ1 hl1 "u" u hu (by simp [hτ1, hu']))
        (hlab τ1 hl1 "v" v hv (by simp [hτ1, hv']))]
      simp [hLuv]
    · simp [ind, RSplit, hLuv]
  have hc0 : (Cond.eq (.get "lab" (.var "u")) (.get "lab" (.var "v"))).evalB B τ1 = some true := by
    rw [evalB_condEq' (hlab τ1 hl1 "u" u hu (by simp [hτ1, hu']))
      (hlab τ1 hl1 "v" v hv (by simp [hτ1, hv']))]
    simp [hLuv]
  let P : ℕ → Prop := fun z => L z = z → L z ≠ L u → (A u z ↔ A v z)
  let Z : ℕ → Env → Prop := fun k ρ => MatCtx n t X A ρ ∧ LabAt n L ρ ∧ ρ.vars "u" = u ∧
    ρ.vars "v" = v ∧ ρ.vars "ok" = ind (∀ z < k, P z)
  obtain ⟨ρ, hrz, ⟨-, -, -, -, hokρ⟩, -⟩ :=
    forUp_run (B := B) (i := "z") (e := .var "n") (body := zstepQ) (N := n) (K := 40) Z
      (by omega) (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
      (σ := τ1) ⟨hc1.of_eq (by simp) (by simp) rfl rfl, by simpa [LabAt] using hl1,
        by simp [hτ1, hu'], by simp [hτ1, hv'], by simp [hτ1, ind]⟩
      (by
        rintro k hk ρ ⟨hcρ, hlρ, huρ, hvρ, hokρ⟩ hzk
        have hlz := hlab ρ hlρ "z" k hk hzk
        have hlu := hlab ρ hlρ "u" u hu huρ
        have hau := hadj ρ hcρ "u" u hu huρ k hk hzk
        have hav := hadj ρ hcρ "v" v hv hvρ k hk hzk
        have hsucc : (∀ z < k + 1, P z) ↔ ((∀ z < k, P z) ∧ P k) := by
          constructor
          · intro h; exact ⟨fun z hz => h z (by omega), h k (by omega)⟩
          · rintro ⟨h1, h2⟩ z hz
            rcases Nat.lt_succ_iff_lt_or_eq.mp hz with hz | rfl
            · exact h1 z hz
            · exact h2
        have hfin : ∀ ρ' : Env, ρ'.vars "z" = k → MatCtx n t X A ρ' → LabAt n L ρ' →
            ρ'.vars "u" = u → ρ'.vars "v" = v → ρ'.vars "ok" = ind (∀ z < k + 1, P z) →
            Z (k + 1) (ρ'.setVar "z" (k + 1)) := fun ρ' _ h1 h0 h2 h3 h4 =>
          ⟨h1.of_eq (by simp) (by simp) rfl rfl, by simpa [LabAt] using h0, by simp [h2],
            by simp [h3], by simp [h4]⟩
        have hkeep : P k → ρ.vars "ok" = ind (∀ z < k + 1, P z) := fun hP => by
          rw [hokρ]; exact ind_eq_iff.mpr (by rw [hsucc]; exact ⟨fun h => ⟨h, hP⟩, And.left⟩)
        have hzv : (Expr.var "z").evalB B ρ = some k := by rw [evalB_var (by omega), hzk]
        by_cases hmin : L k = k
        · have hc' : (Cond.eq (.get "lab" (.var "z")) (.var "z")).evalB B ρ = some true := by
            rw [evalB_condEq' hlz hzv]; simp [hmin]
          by_cases hsame : L k = L u
          · refine ⟨ρ, (Run.ite_true hc' (Run.ite_true ?_ Run.skip)).mono (by simp), hzk,
              hfin ρ hzk hcρ hlρ huρ hvρ (hkeep fun _ h => absurd hsame h)⟩
            rw [evalB_condEq' hlz hlu]; simp [hsame]
          have hc2 : (Cond.eq (.get "lab" (.var "z")) (.get "lab" (.var "u"))).evalB B ρ =
              some false := by
            rw [evalB_condEq' hlz hlu]; simp [hsame]
          by_cases hA : (A u k ↔ A v k)
          · refine ⟨ρ, (Run.ite_true hc' (Run.ite_false hc2 (Run.ite_true ?_ Run.skip))).mono
              (by simp), hzk, hfin ρ hzk hcρ hlρ huρ hvρ (hkeep fun _ _ => hA)⟩
            rw [evalB_condEq' hau hav]; simp [ind_eq_iff.mpr hA]
          · refine ⟨ρ.setVar "ok" 0, (Run.ite_true hc' (Run.ite_false hc2 (Run.ite_false ?_
              (Run.assign (v := 0) (by simp; omega))))).mono (by simp), by simp [hzk],
              hfin _ (by simp [hzk]) (hcρ.of_eq (by simp) (by simp) rfl rfl)
                (by simpa [LabAt] using hlρ) (by simp [huρ]) (by simp [hvρ]) ?_⟩
            · rw [evalB_condEq' hau hav]
              simp only [Option.some.injEq, decide_eq_false_iff_not]
              exact fun h => hA (ind_eq_iff.mp h)
            · simp only [vars_setVar, if_true]
              have : ¬ (∀ z < k + 1, P z) := fun h => hA (h k (by omega) hmin hsame)
              simp only [ind]; rw [if_neg this]
        · have hc' : (Cond.eq (.get "lab" (.var "z")) (.var "z")).evalB B ρ = some false := by
            rw [evalB_condEq' hlz hzv]; simp [hmin]
          exact ⟨ρ, (Run.ite_false hc' Run.skip).mono (by simp), hzk,
            hfin ρ hzk hcρ hlρ huρ hvρ (hkeep fun h => absurd h hmin)⟩)
  refine ⟨ρ, (Run.seq h1 (Run.ite_true hc0 hrz)).mono (by simp; omega), ?_⟩
  rw [hokρ]
  exact ind_eq_iff.mpr (by simp [RSplit, hLuv, P])

end Lax185574Proofs.Conversions.Ram
