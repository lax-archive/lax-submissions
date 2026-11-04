import Lax185574Proofs.MainRam.ValidChk

/-!
The validation program, part four: the loops of checks on the opcodes,
the injectivity of the initial colors, the final colors and the final
statuses, and the filling of the color vector.
-/

namespace Lax185574Proofs.MainRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Classical

/-- The frame of a phase: only the scalars in `wl` and no array changed. -/
def Fr (σ : Env) (wl : List String) (τ : Env) : Prop :=
  (∀ z, z ∉ wl → τ.vars z = σ.vars z) ∧ τ.arrs = σ.arrs ∧ τ.inp = σ.inp ∧ τ.out = σ.out

theorem Fr.refl (σ : Env) (wl : List String) : Fr σ wl σ := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Fr.setVar {σ τ : Env} {wl : List String} (h : Fr σ wl τ) {x : String} (hx : x ∈ wl)
    (v : ℕ) : Fr σ wl (τ.setVar x v) :=
  ⟨fun z hz => by simp [show z ≠ x from fun e => hz (e ▸ hx), h.1 z hz], h.2.1, h.2.2.1, h.2.2.2⟩

theorem Fr.var {σ τ : Env} {wl : List String} (h : Fr σ wl τ) {z : String} (hz : z ∉ wl) :
    τ.vars z = σ.vars z := h.1 z hz

theorem Fr.arr {σ τ : Env} {wl : List String} (h : Fr σ wl τ) (a : String) :
    τ.arrs a = σ.arrs a := by rw [h.2.1]

/-- The frame survives a check. -/
theorem Fr.chk {σ τ τ' : Env} {wl : List String} (h : Fr σ wl τ) (hok : "ok" ∈ wl)
    (hv : ∀ z, z ≠ "ok" → τ'.vars z = τ.vars z) (ha : τ'.arrs = τ.arrs) (hi : τ'.inp = τ.inp)
    (ho : τ'.out = τ.out) : Fr σ wl τ' :=
  ⟨fun z hz => by rw [hv z (fun e => hz (e ▸ hok)), h.1 z hz], by rw [ha, h.2.1],
    by rw [hi, h.2.2.1], by rw [ho, h.2.2.2]⟩

theorem getD_le {y : List ℕ} {Λ : ℕ} (h : ∀ a ∈ y, a ≤ Λ) (i : ℕ) : y.getD i 0 ≤ Λ := by
  rcases Nat.lt_or_ge i y.length with hi | hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]; exact Nat.zero_le _

/-! ### Opcodes -/

def opPh : Com := forUp "t" (.var "m") (chkIf (.lt (.get "Y" opIdx) (.lit 3)))

theorem evalB_opIdx {B n t : ℕ} {τ : Env} (hn : τ.vars "n" = n) (ht : τ.vars "t" = t)
    (hB : n + 2 + 3 * t + 2 < B) : opIdx.evalB B τ = some (n + 2 + 3 * t) := by
  have e1 := evalB_bin (op := .add) (evalB_var (B := B) (σ := τ) (x := "n") (by rw [hn]; omega))
    (evalB_lit (n := 2) (σ := τ) (by omega)) (by show τ.vars "n" + 2 < B; rw [hn]; omega)
  have e2 := evalB_bin (op := .mul) (evalB_lit (n := 3) (B := B) (σ := τ) (by omega))
    (evalB_var (x := "t") (by rw [ht]; omega)) (by show 3 * τ.vars "t" < B; rw [ht]; omega)
  have e3 := evalB_bin (op := .add) e1 e2 (by show τ.vars "n" + 2 + 3 * τ.vars "t" < B; rw [hn, ht]; omega)
  unfold opIdx; rw [e3]; simp [hn, ht]

theorem opPh_run {B Λ M : ℕ} {τ : Env} {n : ℕ} {y : List ℕ} (hn : τ.vars "n" = n)
    (hm : τ.vars "m" = M) (hY : τ.arrs "Y" = y) (hyΛ : ∀ a ∈ y, a ≤ Λ)
    (hlen : n + 2 + 3 * M ≤ y.length) (hlΛ : y.length ≤ Λ) (hB : 4 * Λ + 8 < B) :
    ∃ τ', Run B opPh τ τ' (M * 30 + 6) ∧ Fr τ ["t", "ok"] τ' ∧
      τ'.vars "ok" = if (∀ t < M, y.getD (n + 2 + 3 * t) 0 < 3) then τ.vars "ok" else 0 := by
  obtain ⟨τ', hr, hC, hok⟩ := chk_run (B := B) (N := M) (K := 19) (i := "t") (e := .var "m")
    (body := chkIf (.lt (.get "Y" opIdx) (.lit 3))) (Fr τ ["t", "ok"])
    (fun t => y.getD (n + 2 + 3 * t) 0 < 3) (by omega) (by decide)
    (fun ρ h => by rw [evalB_var (by rw [h.var (by decide), hm]; omega), h.var (by decide), hm])
    (fun ρ x h => h.setVar (by decide) x)
    (by
      intro k hk ρ hρ hk'
      have hi : n + 2 + 3 * k < y.length := by omega
      have hidx := evalB_opIdx (B := B) (by rw [hρ.var (z := "n") (by decide), hn]) hk' (by omega)
      have hle := getD_le hyΛ (n + 2 + 3 * k)
      obtain ⟨ρ', r, hok, hv, ha, hi', ho⟩ := chkIf_run (B := B) (τ := ρ)
        (c := .lt (.get "Y" opIdx) (.lit 3)) (P := y.getD (n + 2 + 3 * k) 0 < 3) (by omega)
        (evalB_condLt_isSome (evalB_get hidx (by rw [hρ.arr, hY]; exact getY hi)
          (by omega)) (evalB_lit (by omega)))
      exact ⟨ρ', r.mono (by simp [opIdx]), hρ.chk (by decide) hv ha hi' ho,
          by rw [hv _ (by decide), hk'], hok⟩)
    (Fr.refl τ _)
  exact ⟨τ', hr.mono (by simp <;> omega), hC, by rw [hok]; try (split_ifs <;> rfl)⟩

theorem Fr.trans {σ τ ρ : Env} {wl wl' : List String} (h1 : Fr σ wl' τ) (h2 : Fr τ wl ρ)
    (hsub : ∀ z, z ∈ wl → z ∈ wl') : Fr σ wl' ρ :=
  ⟨fun z hz => by rw [h2.1 z (fun h => hz (hsub z h)), h1.1 z hz], by rw [h2.2.1, h1.2.1],
    by rw [h2.2.2.1, h1.2.2.1], by rw [h2.2.2.2, h1.2.2.2]⟩

theorem ind_mul_ind (p q : Prop) : ind p * ind q = ind (p ∧ q) := by
  unfold ind; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem ind_lt_B {B : ℕ} (p : Prop) (hB : 1 < B) : ind p < B := by
  have := ind_le_one p; omega

/-! ### The initial colors -/

def colPh : Com := rowFill "col" (.var "b") (.get "Y" (.add (.var "b") (.lit 1)))

theorem colPh_run {B Λ : ℕ} {σ : Env} {n : ℕ} {y : List ℕ} (hn : σ.vars "n" = n)
    (hY : σ.arrs "Y" = y) (hcol : (σ.arrs "col").length = n) (hyΛ : ∀ a ∈ y, a ≤ Λ)
    (hlen : n + 1 ≤ y.length) (hlΛ : y.length ≤ Λ) (hB : 4 * Λ + 8 < B) :
    ∃ σ', Run B colPh σ σ' (n * 16 + 6) ∧ Vec σ' "col" n (fun v => y.getD (v + 1) 0) ∧
      (∀ z, z ≠ "b" → σ'.vars z = σ.vars z) ∧ (∀ a, a ≠ "col" → σ'.arrs a = σ.arrs a) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  let Ctx : Env → Prop := fun τ => τ.vars "n" = n ∧ τ.arrs "Y" = y ∧
    (∀ z, z ≠ "b" → τ.vars z = σ.vars z) ∧ (∀ a, a ≠ "col" → τ.arrs a = σ.arrs a) ∧
    τ.inp = σ.inp ∧ τ.out = σ.out
  obtain ⟨σ', hr, ⟨-, -, hv, ha, hi, ho⟩, hl, hg⟩ := rowFill_run (B := B) (n := n) (base := 0)
    (K := 8) (arr := "col") (ie := .var "b") (e := .get "Y" (.add (.var "b") (.lit 1))) Ctx
    (fun v => y.getD (v + 1) 0) (by omega) (fun τ h => h.1)
    (fun τ x h => ⟨by simp [h.1], by simp [h.2.1], fun z hz => by simp [hz, h.2.2.1 z hz],
      fun a ha => by simp [h.2.2.2.1 a ha], by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2]⟩)
    (fun τ i x h => ⟨by simp [h.1], by simp [h.2.1], fun z hz => by simp [h.2.2.1 z hz],
      fun a ha => by simp [ha, h.2.2.2.1 a ha], by simp [h.2.2.2.2.1], by simp [h.2.2.2.2.2]⟩)
    (fun τ k h hb hk => by rw [evalB_var (by rw [hb]; omega), hb]; simp)
    (fun τ k h hb hk => by
      have hidx := evalB_bin (op := .add) (evalB_var (B := B) (σ := τ) (x := "b")
        (by rw [hb]; omega)) (evalB_lit (n := 1) (σ := τ) (by omega))
        (by show τ.vars "b" + 1 < B; rw [hb]; omega)
      rw [show Bop.add.apply (τ.vars "b") 1 = k + 1 by simp [hb]] at hidx
      exact evalB_get hidx (by rw [h.2.1]; exact getY (by omega))
        (by have := getD_le hyΛ (k + 1); omega))
    (by simp) ⟨hn, hY, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩ (by omega)
  refine ⟨σ', hr.mono (by omega), ⟨by rw [hl, hcol], fun i hi => ?_⟩, hv, ha, hi, ho⟩
  rw [hg i, if_pos ⟨Nat.zero_le _, by omega⟩]; simp

/-! ### Injectivity of the initial colors -/

def injCond : Cond :=
  .eq (.mul (.sub (.lit 1) (eqE "a" "b")) (eqX (.get "col" (.var "a")) (.get "col" (.var "b"))))
    (.lit 0)

def injPh : Com := forUp "a" (.var "n") (forUp "b" (.var "n") (chkIf injCond))

theorem injPh_run {B Λ : ℕ} {σ : Env} {n : ℕ} {c : ℕ → ℕ} (hn : σ.vars "n" = n)
    (hc : Vec σ "col" n c) (hcΛ : ∀ v < n, c v ≤ Λ) (hnΛ : n ≤ Λ) (hB : 4 * Λ + 8 < B) :
    ∃ σ', Run B injPh σ σ' (n * (n * 70 + 14) + 6) ∧ Fr σ ["a", "b", "ok"] σ' ∧
      σ'.vars "ok" = if (∀ u < n, ∀ v < n, ¬ (u ≠ v ∧ c u = c v)) then σ.vars "ok" else 0 := by
  obtain ⟨σ', hr, hC, hok⟩ := chk_run (B := B) (N := n) (K := n * 70 + 6) (i := "a")
    (e := .var "n") (body := forUp "b" (.var "n") (chkIf injCond)) (Fr σ ["a", "b", "ok"])
    (fun u => ∀ v < n, ¬ (u ≠ v ∧ c u = c v)) (by omega) (by decide)
    (fun ρ h => by rw [evalB_var (by rw [h.var (by decide), hn]; omega), h.var (by decide), hn])
    (fun ρ x h => h.setVar (by decide) x)
    (by
      intro u hu ρ hρ hu'
      obtain ⟨ρ', hr', hC', hok'⟩ := chk_run (B := B) (N := n) (K := 60) (i := "b")
        (e := .var "n") (body := chkIf injCond) (Fr ρ ["b", "ok"])
        (fun v => ¬ (u ≠ v ∧ c u = c v)) (by omega) (by decide)
        (fun τ h => by
          rw [evalB_var (by rw [h.var (by decide), hρ.var (by decide), hn]; omega),
            h.var (by decide), hρ.var (by decide), hn])
        (fun τ x h => h.setVar (by decide) x)
        (by
          intro v hv τ hτ hv'
          have hua : τ.vars "a" = u := by rw [hτ.var (by decide), hu']
          have hcol : Vec τ "col" n c := hc.of_eq (by rw [hτ.arr, hρ.arr])
          have hcu := hcΛ u hu
          have hcv := hcΛ v hv
          have e1 := evalB_eqE (B := B) (σ := τ) (x := "a") (y := "b") (by rw [hua]; omega)
            (by rw [hv']; omega) (by omega)
          rw [hua, hv'] at e1
          have e2 := evalB_bin (op := .sub) (evalB_lit (n := 1) (B := B) (σ := τ) (by omega)) e1
            (by have := ind_le_one (u = v); simp; omega)
          rw [Bop.apply_sub, one_sub_ind] at e2
          have e3 := evalB_eqX (B := B) (Vec.evalB (B := B) hcol hua hu (by omega) (by omega))
            (Vec.evalB (B := B) hcol hv' hv (by omega) (by omega)) (by omega) (by omega) (by omega)
          have e4 := evalB_bin (op := .mul) e2 e3 (by rw [Bop.apply_mul, ind_mul_ind]; exact ind_lt_B _ (by omega))
          rw [Bop.apply_mul, ind_mul_ind] at e4
          obtain ⟨τ', r, hok, hvv, ha, hi, ho⟩ := chkIf_run (B := B) (τ := τ) (c := injCond)
            (P := ¬ (u ≠ v ∧ c u = c v)) (by omega)
            ⟨_, evalB_condEq' e4 (evalB_lit (n := 0) (by omega)), by
              by_cases h : (u ≠ v ∧ c u = c v) <;> simp [ind, h]⟩
          exact ⟨τ', r.mono (by simp [injCond]), hτ.chk (by decide) hvv ha hi ho,
            by rw [hvv _ (by decide), hv'], hok⟩)
        (Fr.refl ρ _)
      refine ⟨ρ', hr'.mono (by simp <;> omega), hρ.trans hC' (by decide), ?_, ?_⟩
      · rw [hC'.var (by decide), hu']
      · rw [hok']; try (split_ifs <;> rfl))
    (Fr.refl σ _)
  exact ⟨σ', hr.mono (by simp <;> omega), hC, by rw [hok]; try (split_ifs <;> rfl)⟩

/-! ### The final colors -/

def finColPh : Com := forUp "b" (.var "n") (chkIf (.eq (.get "col" (.var "b")) (.get "col" (.lit 0))))

theorem finColPh_run {B Λ : ℕ} {σ : Env} {n : ℕ} {c : ℕ → ℕ} (hn : σ.vars "n" = n)
    (hc : Vec σ "col" n c) (hcΛ : ∀ v < n, c v ≤ Λ) (hnΛ : n ≤ Λ) (hB : 4 * Λ + 8 < B) :
    ∃ σ', Run B finColPh σ σ' (n * 20 + 6) ∧ Fr σ ["b", "ok"] σ' ∧
      σ'.vars "ok" = if (∀ v < n, c v = c 0) then σ.vars "ok" else 0 := by
  obtain ⟨σ', hr, hC, hok⟩ := chk_run (B := B) (N := n) (K := 12) (i := "b")
    (e := .var "n") (body := chkIf (.eq (.get "col" (.var "b")) (.get "col" (.lit 0))))
    (Fr σ ["b", "ok"]) (fun v => c v = c 0) (by omega) (by decide)
    (fun ρ h => by rw [evalB_var (by rw [h.var (by decide), hn]; omega), h.var (by decide), hn])
    (fun ρ x h => h.setVar (by decide) x)
    (by
      intro v hv τ hτ hv'
      have hcol : Vec τ "col" n c := hc.of_eq (by rw [hτ.arr])
      have h0 : 0 < n := by omega
      have e1 := Vec.evalB (B := B) hcol hv' hv (by omega) (by have := hcΛ v hv; omega)
      have e2 : (Expr.get "col" (.lit 0)).evalB B τ = some (c 0) :=
        evalB_get (evalB_lit (by omega)) (hcol.get 0 h0) (by have := hcΛ 0 h0; omega)
      obtain ⟨τ', r, hok, hvv, ha, hi, ho⟩ := chkIf_run (B := B) (τ := τ)
        (c := .eq (.get "col" (.var "b")) (.get "col" (.lit 0))) (P := c v = c 0) (by omega)
        ⟨_, evalB_condEq' e1 e2, by simp⟩
      exact ⟨τ', r.mono (by simp), hτ.chk (by decide) hvv ha hi ho,
        by rw [hvv _ (by decide), hv'], hok⟩)
    (Fr.refl σ _)
  exact ⟨σ', hr.mono (by simp <;> omega), hC, by rw [hok]; try (split_ifs <;> rfl)⟩

/-! ### The final statuses -/

def finE : Expr :=
  .or (eqE "a" "b") (.or (.and (eqX (.get "S" (rm "a" "b")) (.lit 1)) (.get "A" (rm "a" "b")))
    (.and (eqX (.get "S" (rm "a" "b")) (.lit 2)) (.sub (.lit 1) (.get "A" (rm "a" "b")))))

def finMatPh : Com := forUp "a" (.var "n") (forUp "b" (.var "n") (chkIf (.eq finE (.lit 1))))

theorem finMatPh_run {B Λ : ℕ} {σ : Env} {n : ℕ} {st : ℕ → ℕ → ℕ} {Q : ℕ → ℕ → Prop}
    (hn : σ.vars "n" = n) (hS : Mat σ "S" n st) (hA : Mat σ "A" n (fun u v => ind (Q u v)))
    (hsΛ : ∀ u < n, ∀ v < n, st u v ≤ Λ) (hnΛ : n * n + n ≤ Λ) (hB : 4 * Λ + 8 < B) :
    ∃ σ', Run B finMatPh σ σ' (n * (n * 120 + 14) + 6) ∧ Fr σ ["a", "b", "ok"] σ' ∧
      σ'.vars "ok" = if (∀ u < n, ∀ v < n,
        u = v ∨ (st u v = 1 ∧ Q u v) ∨ (st u v = 2 ∧ ¬ Q u v)) then σ.vars "ok" else 0 := by
  obtain ⟨σ', hr, hC, hok⟩ := chk_run (B := B) (N := n) (K := n * 120 + 6) (i := "a")
    (e := .var "n") (body := forUp "b" (.var "n") (chkIf (.eq finE (.lit 1))))
    (Fr σ ["a", "b", "ok"])
    (fun u => ∀ v < n, u = v ∨ (st u v = 1 ∧ Q u v) ∨ (st u v = 2 ∧ ¬ Q u v)) (by omega)
    (by decide)
    (fun ρ h => by rw [evalB_var (by rw [h.var (by decide), hn]; omega), h.var (by decide), hn])
    (fun ρ x h => h.setVar (by decide) x)
    (by
      intro u hu ρ hρ hu'
      obtain ⟨ρ', hr', hC', hok'⟩ := chk_run (B := B) (N := n) (K := 110) (i := "b")
        (e := .var "n") (body := chkIf (.eq finE (.lit 1))) (Fr ρ ["b", "ok"])
        (fun v => u = v ∨ (st u v = 1 ∧ Q u v) ∨ (st u v = 2 ∧ ¬ Q u v)) (by omega) (by decide)
        (fun τ h => by
          rw [evalB_var (by rw [h.var (by decide), hρ.var (by decide), hn]; omega),
            h.var (by decide), hρ.var (by decide), hn])
        (fun τ x h => h.setVar (by decide) x)
        (by
          intro v hv τ hτ hv'
          have hua : τ.vars "a" = u := by rw [hτ.var (by decide), hu']
          have hnτ : τ.vars "n" = n := by rw [hτ.var (by decide), hρ.var (by decide), hn]
          have hSτ : Mat τ "S" n st := hS.of_eq (by rw [hτ.arr, hρ.arr])
          have hAτ : Mat τ "A" n (fun u v => ind (Q u v)) := hA.of_eq (by rw [hτ.arr, hρ.arr])
          have hsuv := hsΛ u hu v hv
          have hnn : n * n < B := by omega
          have eS := Mat.evalB (B := B) hSτ hnτ hua hv' hu hv hnn (by omega) (by omega)
          have eA := Mat.evalB (B := B) hAτ hnτ hua hv' hu hv hnn (by omega)
            (ind_lt_B _ (by omega))
          have e0 := evalB_eqE (B := B) (σ := τ) (x := "a") (y := "b") (by rw [hua]; omega)
            (by rw [hv']; omega) (by omega)
          rw [hua, hv'] at e0
          have e1 := evalB_eqX (B := B) eS (evalB_lit (n := 1) (by omega)) (by omega) (by omega)
            (by omega)
          have e2 := evalB_eqX (B := B) eS (evalB_lit (n := 2) (by omega)) (by omega) (by omega)
            (by omega)
          have e3 := evalB_bin (op := .and) e1 eA
            (by rw [Bop.apply_and, land_ind]; exact ind_lt_B _ (by omega))
          rw [Bop.apply_and, land_ind] at e3
          have e4 := evalB_bin (op := .sub) (evalB_lit (n := 1) (B := B) (σ := τ) (by omega)) eA
            (by have := ind_le_one (Q u v); simp; omega)
          rw [Bop.apply_sub, one_sub_ind] at e4
          have e5 := evalB_bin (op := .and) e2 e4
            (by rw [Bop.apply_and, land_ind]; exact ind_lt_B _ (by omega))
          rw [Bop.apply_and, land_ind] at e5
          have e6 := evalB_bin (op := .or) e3 e5
            (by rw [Bop.apply_or, lor_ind]; exact ind_lt_B _ (by omega))
          rw [Bop.apply_or, lor_ind] at e6
          have e7 := evalB_bin (op := .or) e0 e6
            (by rw [Bop.apply_or, lor_ind]; exact ind_lt_B _ (by omega))
          rw [Bop.apply_or, lor_ind] at e7
          obtain ⟨τ', r, hok, hvv, ha, hi, ho⟩ := chkIf_run (B := B) (τ := τ)
            (c := .eq finE (.lit 1)) (P := u = v ∨ (st u v = 1 ∧ Q u v) ∨ (st u v = 2 ∧ ¬ Q u v))
            (by omega) ⟨_, evalB_condEq' e7 (evalB_lit (n := 1) (by omega)), by
              rw [decide_eq_true_iff, ind_eq_one]⟩
          exact ⟨τ', r.mono (by simp [finE]), hτ.chk (by decide) hvv ha hi ho,
            by rw [hvv _ (by decide), hv'], hok⟩)
        (Fr.refl ρ _)
      refine ⟨ρ', hr'.mono (by simp <;> omega), hρ.trans hC' (by decide), ?_, ?_⟩
      · rw [hC'.var (by decide), hu']
      · rw [hok']; try (split_ifs <;> rfl))
    (Fr.refl σ _)
  exact ⟨σ', hr.mono (by simp <;> omega), hC, by rw [hok]; try (split_ifs <;> rfl)⟩

end Lax185574Proofs.MainRam
