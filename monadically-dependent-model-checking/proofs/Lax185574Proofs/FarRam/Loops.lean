import Lax185574Proofs.FarRam.Pure
import Lax185574Proofs.Words.ForLoop
import Lax185574Proofs.Words.Select


/-!
Loop shapes of the far-tree program.

`findLoop` returns the first index of a range whose test succeeds, and a
default if there is none. `anyLoop` sets a flag if the test succeeds for
some index. `powLoop` computes a power. `hitC` looks up the atom
`dist(xᵢ, xⱼ) ≤ s` in the node at a position of `x`. A context
predicate `C` that the bodies keep is carried through each loop.
-/

namespace Lax185574Proofs.FarRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.EvalRam

/-! ### Searching a range -/

/-- Run `body` for `i = lo, lo + 1, …` below `hi` until it sets `v` to `1`,
and record that `i` in `res`. -/
def findLoop (i hi res v : String) (body : Com) : Com :=
  .while (.lt (.var i) (.var hi))
    (.seq body (.ite (.eq (.var v) (.lit 1)) (.seq (.assign res (.var i)) (.assign i (.var hi)))
      (.assign i (.add (.var i) (.lit 1)))))

theorem find_range'_some {f : ℕ → Bool} {lo c H : ℕ} (hlo : lo ≤ c) (hc : c < H)
    (hpre : ∀ c', lo ≤ c' → c' < c → f c' = false) (hf : f c = true) :
    (List.range' lo (H - lo)).find? f = some c := by
  have hsplit : List.range' lo (H - lo) = List.range' lo (c - lo) ++ c :: List.range' (c + 1) (H - c - 1) := by
    rw [show H - lo = (c - lo) + (H - c - 1 + 1) by omega, ← List.range'_append, Nat.one_mul,
      show lo + (c - lo) = c by omega, List.range'_succ]
  rw [hsplit, List.find?_append, List.find?_eq_none.mpr]
  · simp [hf]
  · intro x hx
    rw [List.mem_range'] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    simp [hpre (lo + j) (by omega) (by omega)]

theorem find_range'_none {f : ℕ → Bool} {lo H : ℕ} (hpre : ∀ c', lo ≤ c' → c' < H → f c' = false) :
    (List.range' lo (H - lo)).find? f = none := by
  rw [List.find?_eq_none]
  intro x hx
  rw [List.mem_range'] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  simp [hpre (lo + j) (by omega) (by omega)]

/-- **The search loop.** -/
theorem findLoop_run {B : ℕ} {i hi res v : String} {body : Com} (C : Env → Prop) (f : ℕ → Bool)
    (lo H d Kb : ℕ) (hHB : H + 1 < B) (hd : d < B) (h1 : i ≠ hi) (h2 : i ≠ res) (h3 : hi ≠ res)
    (hCi : ∀ τ x, C τ → C (τ.setVar i x)) (hCr : ∀ τ x, C τ → C (τ.setVar res x))
    (hbody : ∀ c, lo ≤ c → c < H → Spec B (fun τ => C τ ∧ τ.vars i = c ∧ τ.vars hi = H ∧
        τ.vars res = d) body (fun _ τ' => C τ' ∧ τ'.vars i = c ∧ τ'.vars hi = H ∧
        τ'.vars res = d ∧ τ'.vars v = bv (f c)) Kb)
    (σ : Env) (hσ : C σ ∧ σ.vars i = lo ∧ σ.vars hi = H ∧ σ.vars res = d) (hlo : lo ≤ H) :
    ∃ σ', Run B (findLoop i hi res v body) σ σ' ((Kb + 20) * (H - lo) + 4) ∧ C σ' ∧
      σ'.vars res = ((List.range' lo (H - lo)).find? f).getD d ∧ σ'.vars hi = H := by
  let I : Env → Prop := fun τ => C τ ∧ τ.vars hi = H ∧ lo ≤ τ.vars i ∧ τ.vars i ≤ H ∧
    (((∀ c', lo ≤ c' → c' < τ.vars i → f c' = false) ∧ τ.vars res = d) ∨
      (τ.vars i = H ∧ τ.vars res = ((List.range' lo (H - lo)).find? f).getD d))
  obtain ⟨σ', hr, hI, hfalse⟩ := Run.while_count (B := B) (b := .lt (.var i) (.var hi))
    (c := .seq body (.ite (.eq (.var v) (.lit 1)) (.seq (.assign res (.var i)) (.assign i (.var hi)))
      (.assign i (.add (.var i) (.lit 1))))) I (fun τ => H - τ.vars i) (Kb + 16)
    (fun τ hτ => evalB_condLt_vars (by omega) (by omega))
    (by
      rintro τ ⟨hC, hhi, hlo', hle, hcase⟩ hc
      have hlt : τ.vars i < H := by have := lt_of_condLt_true hc; omega
      have hs : ((∀ c', lo ≤ c' → c' < τ.vars i → f c' = false) ∧ τ.vars res = d) := by
        rcases hcase with h | h
        · exact h
        · omega
      obtain ⟨τ1, hr1, hC1, hi1, hhi1, hres1, hv1⟩ := hbody (τ.vars i) hlo' hlt τ ⟨hC, rfl, hhi, hs.2⟩
      have hvB : τ1.vars v < B := by rw [hv1]; have := bv_le (f (τ.vars i)); omega
      by_cases hf : f (τ.vars i) = true
      · have hv : τ1.vars v = 1 := by rw [hv1, hf]; rfl
        refine ⟨(τ1.setVar res (τ.vars i)).setVar i H, (Run.seq hr1 (Run.ite_true ?_
          (Run.seq (Run.assign ?_) (Run.assign ?_)))).mono ?_, ⟨hCi _ _ (hCr _ _ hC1), ?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [eq_true_iff' hvB (by omega), hv]; rfl
        · simp only [evalB_var_iff]; exact ⟨hi1.symm, by omega⟩
        · simp only [evalB_var_iff, vars_setVar, if_neg h3]; exact ⟨hhi1.symm, by omega⟩
        · simp <;> omega
        · simp [vars_setVar, if_neg (Ne.symm h1), if_neg h3, hhi1]
        · simp <;> omega
        · simp
        · right
          refine ⟨by simp, ?_⟩
          simp only [vars_setVar, if_neg (Ne.symm h2), if_true]
          rw [find_range'_some hlo' hlt hs.1 hf]; rfl
        · simp <;> omega
      · have hv : τ1.vars v = 0 := by rw [hv1]; simp at hf; simp [hf]
        refine ⟨τ1.setVar i (τ.vars i + 1), (Run.seq hr1 (Run.ite_false ?_ (Run.assign ?_))).mono ?_,
          ⟨hCi _ _ hC1, ?_, ?_, ?_, ?_⟩, ?_⟩
        · rw [eq_true_iff' hvB (by omega), hv]; rfl
        · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
          exact ⟨τ.vars i, 1, ⟨hi1.symm, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
        · simp <;> omega
        · simp [vars_setVar, if_neg (Ne.symm h1), hhi1]
        · simp <;> omega
        · simp <;> omega
        · left
          refine ⟨fun c' hc1 hc2 => ?_, by simp [vars_setVar, if_neg (Ne.symm h2), hres1]⟩
          simp only [vars_setVar, if_true] at hc2
          rcases Nat.lt_or_ge c' (τ.vars i) with h | h
          · exact hs.1 c' hc1 h
          · have : c' = τ.vars i := by omega
            subst this; simpa using hf
        · simp; omega)
    ⟨hσ.1, hσ.2.2.1, by omega, by omega, Or.inl ⟨fun c' h h' => by omega, hσ.2.2.2⟩⟩
  obtain ⟨hC, hhi, -, hle, hcase⟩ := hI
  have hge : H ≤ σ'.vars i := by have := le_of_condLt_false hfalse; omega
  refine ⟨σ', hr.mono ?_, hC, ?_, hhi⟩
  · simp only [Cond.size, Expr.size, hσ.2.1]
    nlinarith
  · rcases hcase with ⟨hall, hres⟩ | ⟨-, hres⟩
    · rw [hres, find_range'_none (fun c' h h' => hall c' h (by omega))]; rfl
    · exact hres

/-! ### Counting loops with a varying cost -/

/-- **The counting loop with a cost per round.** -/
theorem forUp_run_sum {B : ℕ} {i : String} {e : Expr} {body : Com} {N : ℕ} (Kf : ℕ → ℕ)
    (I : ℕ → Env → Prop) {σ : Env} (hN : N < B)
    (he : ∀ k ≤ N, ∀ τ, I k τ → τ.vars i = k → e.evalB B τ = some N)
    (h0 : I 0 (σ.setVar i 0))
    (hstep : ∀ k < N, ∀ τ, I k τ → τ.vars i = k →
      ∃ τ', Run B body τ τ' (Kf k) ∧ τ'.vars i = k ∧ I (k + 1) (τ'.setVar i (k + 1))) :
    ∃ σ', Run B (forUp i e body) σ σ' ((∑ k ∈ Finset.range N, (Kf k + e.size + 7)) + e.size + 5) ∧
      I N σ' ∧ σ'.vars i = N := by
  let Φ : Env → ℕ := fun τ => ∑ k ∈ Finset.Ico (τ.vars i) N, (Kf k + e.size + 7)
  let J : Env → Prop := fun τ => ∃ k ≤ N, τ.vars i = k ∧ I k τ
  obtain ⟨σ', K, hrun, ⟨k, hk, hik, hI⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var i) e)
      (c := .seq body (.assign i (.add (.var i) (.lit 1)))) J Φ
      (fun τ ⟨k, hk, hik, hI⟩ => ⟨_, evalB_condLt (evalB_var (by omega)) (he k hk τ hI hik)⟩)
      (by
        rintro τ ⟨k, hk, hik, hI⟩ hc
        have hkN : k < N := by
          rw [evalB_condLt (evalB_var (by omega)) (he k hk τ hI hik)] at hc
          simp only [Option.some.injEq, decide_eq_true_eq] at hc
          omega
        obtain ⟨τ', hr, hi', hI'⟩ := hstep k hkN τ hI hik
        refine ⟨τ'.setVar i (k + 1), Kf k + 4, (Run.seq hr (Run.assign ?_)).mono (by simp),
          ⟨k + 1, hkN, by simp, hI'⟩, ?_⟩
        · simp [hi']; omega
        · simp only [Φ, vars_setVar, if_true, hik]
          rw [Finset.sum_eq_sum_Ico_succ_bot hkN]
          simp only [Cond.size, Expr.size]; omega)
      (show J (σ.setVar i 0) from ⟨0, Nat.zero_le _, by simp, h0⟩)
  have hkN : k = N := by
    rw [evalB_condLt (evalB_var (by omega)) (he k hk σ' hI hik)] at hfalse
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega
  rw [hkN] at hI hik
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono ?_, hI, hik⟩
  have h1 : Φ (σ.setVar i 0) = ∑ k ∈ Finset.range N, (Kf k + e.size + 7) := by
    simp only [Φ, vars_setVar, if_true, ← Finset.range_eq_Ico]
  simp only [Cond.size, Expr.size] at hK ⊢
  omega

/-! ### Testing a range -/

/-- Run `body` for `i < n` and set `flag` to `1` when it sets `v` to `1`. -/
def anyLoop (i n flag v : String) (body : Com) : Com :=
  forUp i (.var n) (.seq body (.ite (.eq (.var v) (.lit 1)) (.assign flag (.lit 1)) .skip))

theorem any_range_succ (f : ℕ → Bool) (k : ℕ) :
    (List.range (k + 1)).any f = ((List.range k).any f || f k) := by
  simp [List.range_succ, List.any_append]

/-- **The test loop.** -/
theorem anyLoop_run {B : ℕ} {i n flag v : String} {body : Com} (C : Env → Prop) (f : ℕ → Bool)
    (N Kb : ℕ) (hNB : N + 1 < B) (h1 : i ≠ flag) (h2 : n ≠ flag) (h3 : n ≠ i)
    (hCi : ∀ τ x, C τ → C (τ.setVar i x)) (hCf : ∀ τ x, C τ → C (τ.setVar flag x))
    (hbody : ∀ c < N, Spec B (fun τ => C τ ∧ τ.vars i = c ∧ τ.vars n = N ∧ τ.vars flag ≤ 1) body
      (fun τ τ' => C τ' ∧ τ'.vars i = c ∧ τ'.vars n = N ∧ τ'.vars flag = τ.vars flag ∧
        τ'.vars v = bv (f c)) Kb)
    (σ : Env) (hσ : C σ ∧ σ.vars n = N ∧ σ.vars flag = 0) :
    ∃ σ', Run B (anyLoop i n flag v body) σ σ' (N * (Kb + 20) + 6) ∧ C σ' ∧
      σ'.vars flag = bv ((List.range N).any f) ∧ σ'.vars n = N := by
  obtain ⟨σ', hr, hI, -⟩ := forUp_run (B := B) (i := i) (e := .var n)
    (body := .seq body (.ite (.eq (.var v) (.lit 1)) (.assign flag (.lit 1)) .skip)) (N := N)
    (K := Kb + 10)
    (fun k τ => C τ ∧ τ.vars n = N ∧ τ.vars flag = bv ((List.range k).any f)) (σ := σ) (by omega)
    (fun k _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.1.symm, by omega⟩)
    ⟨hCi _ _ hσ.1, by simp [vars_setVar, if_neg h3, hσ.2.1], by
      simp [vars_setVar, if_neg (Ne.symm h1), hσ.2.2]⟩
    (fun k hk τ hI hik => by
      obtain ⟨hC, hn, hfl⟩ := hI
      obtain ⟨τ1, hr1, hC1, hi1, hn1, hfl1, hv1⟩ := hbody k hk τ ⟨hC, hik, hn, by rw [hfl]; exact bv_le _⟩
      have hvB : τ1.vars v < B := by rw [hv1]; have := bv_le (f k); omega
      by_cases hf : f k = true
      · have hv : τ1.vars v = 1 := by rw [hv1, hf]; rfl
        refine ⟨τ1.setVar flag 1, (Run.seq hr1 (Run.ite_true ?_ (Run.assign ?_))).mono ?_, ?_,
          hCi _ _ (hCf _ _ hC1), ?_, ?_⟩
        · rw [eq_true_iff' hvB (by omega), hv]; rfl
        · exact evalB_lit (by omega)
        · simp
        · simp [vars_setVar, if_neg h1, hi1]
        · simp [vars_setVar, if_neg h2, if_neg h3, hn1]
        · simp [vars_setVar, if_neg (Ne.symm h1), any_range_succ, hf]
      · have hv : τ1.vars v = 0 := by rw [hv1]; simp at hf; simp [hf]
        refine ⟨τ1, (Run.seq hr1 (Run.ite_false ?_ Run.skip)).mono ?_, hi1, hCi _ _ hC1, ?_, ?_⟩
        · rw [eq_true_iff' hvB (by omega), hv]; rfl
        · simp
        · simp [vars_setVar, if_neg h3, hn1]
        · simp only [vars_setVar, if_neg (Ne.symm h1), hfl1, hfl, any_range_succ]
          simp at hf; simp [hf])
  exact ⟨σ', hr.mono (by simp; nlinarith), hI.1, hI.2.2, hI.2.1⟩

/-! ### Contexts kept by a command -/

/-- `C` survives every run of `c` that reads and writes nothing. Such a
run keeps the scalars and arrays it cannot assign to, the lengths of all
arrays and both tapes. -/
def Stable (C : Env → Prop) (c : Com) : Prop :=
  ∀ τ τ', (∀ z, z ∉ c.wvars → τ'.vars z = τ.vars z) → (∀ a, a ∉ c.warrs → τ'.arrs a = τ.arrs a) →
    (∀ a, (τ'.arrs a).length = (τ.arrs a).length) → τ'.out = τ.out → τ'.inp = τ.inp →
    C τ → C τ'

theorem Stable.run {B : ℕ} {C : Env → Prop} {c : Com} {τ τ' : Env} {K : ℕ} (hS : Stable C c)
    (hr : Run B c τ τ' K) (hnr : ¬ c.reads) (hnw : c.NoWrite) (h : C τ) : C τ' :=
  hS τ τ' (fun z hz => hr.frame_var z hz) (fun a ha => hr.frame_arr a ha)
    (fun a => run_length_arrs hr a) (hr.out_eq hnw) (hr.frame_inp hnr) h

theorem Stable.mono {C : Env → Prop} {c d : Com} (h : Stable C d) (hv : ∀ z ∈ c.wvars, z ∈ d.wvars)
    (ha : ∀ a ∈ c.warrs, a ∈ d.warrs) : Stable C c :=
  fun τ τ' h1 h2 h3 h4 h5 hC => h τ τ' (fun z hz => h1 z (fun h' => hz (hv z h')))
    (fun a ha' => h2 a (fun h' => ha' (ha a h'))) h3 h4 h5 hC

theorem Stable.and {C D : Env → Prop} {c : Com} (h : Stable C c) (h' : Stable D c) :
    Stable (fun τ => C τ ∧ D τ) c :=
  fun τ τ' h1 h2 h3 h4 h5 hC => ⟨h τ τ' h1 h2 h3 h4 h5 hC.1, h' τ τ' h1 h2 h3 h4 h5 hC.2⟩

theorem Stable.setVar {C : Env → Prop} {c : Com} (h : Stable C c) {z : String} (hz : z ∈ c.wvars)
    (τ : Env) (x : ℕ) (hC : C τ) : C (τ.setVar z x) :=
  h τ _ (fun y hy => by simp [vars_setVar, show y ≠ z from fun e => hy (e ▸ hz)]) (fun _ _ => rfl)
    (fun _ => rfl) rfl rfl hC

/-- Stability of a concrete context: rewrite the scalars and arrays that
the command cannot change, and the lengths of the others. -/
macro "stab" : tactic => `(tactic| (
  intro τ τ' hv ha hl ho hi h
  simp (disch := decide) only [hv, ha, hl, ho, hi] at h ⊢
  exact h))

/-! ### Powers of nine -/

/-- `x := 9^n`. -/
def powLoop (x i n : String) : Com :=
  .seq (.assign x (.lit 1)) (forUp i (.var n) (.assign x (.mul (.var x) (.lit 9))))

theorem powLoop_run {B : ℕ} {x i n : String} (C : Env → Prop) (N : ℕ) (hB : 9 ^ N < B) (h9 : 9 < B)
    (hNB : N + 1 < B) (h1 : x ≠ i) (h2 : x ≠ n) (h3 : n ≠ i) (hCx : ∀ τ v, C τ → C (τ.setVar x v))
    (hCi : ∀ τ v, C τ → C (τ.setVar i v)) (σ : Env) (hσ : C σ ∧ σ.vars n = N) :
    ∃ σ', Run B (powLoop x i n) σ σ' (N * 20 + 10) ∧ C σ' ∧ σ'.vars x = 9 ^ N ∧ σ'.vars n = N := by
  have hp : ∀ k ≤ N, 9 ^ k < B := fun k hk =>
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) hk) hB
  obtain ⟨σ', hr, hI, -⟩ := forUp_run (B := B) (i := i) (e := .var n)
    (body := .assign x (.mul (.var x) (.lit 9))) (N := N) (K := 6)
    (fun k τ => C τ ∧ τ.vars n = N ∧ τ.vars x = 9 ^ k) (σ := σ.setVar x 1) (by omega)
    (fun k _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.1.symm, by omega⟩)
    ⟨hCi _ _ (hCx _ _ hσ.1), by simp [vars_setVar, if_neg h3, if_neg (Ne.symm h2), hσ.2],
      by simp [vars_setVar, if_neg h1]⟩
    (fun k hk τ hI hik => by
      obtain ⟨hC, hn, hx⟩ := hI
      refine ⟨τ.setVar x (9 ^ (k + 1)), (Run.assign ?_).mono (by simp), ?_, hCi _ _ (hCx _ _ hC),
        ?_, ?_⟩
      · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨9 ^ k, 9, ⟨hx.symm, by rw [hx]; exact hp k hk.le⟩, ⟨rfl, h9⟩, by simp [Bop.apply, pow_succ],
          hp (k + 1) hk⟩
      · simp [vars_setVar, Ne.symm h1, hik]
      · simp [vars_setVar, if_neg h3, if_neg (Ne.symm h2), hn]
      · simp [vars_setVar, if_neg h1])
  exact ⟨σ', (Run.seq (Run.assign (v := 1) (evalB_lit (by omega))) hr).mono (by simp; nlinarith),
    hI.1, hI.2.2, hI.2.1⟩

/-! ### Looking up a distance atom -/

/-- Look up `dist(x_hi, x_hj) ≤ hs` in the node at `hy` of `x`, the
answer in `v`. -/
def hitC : Com :=
  .seq (.store "f" (.lit 0) (.lit 4)) (.seq (.store "f" (.lit 1) (.var "hs"))
    (.seq (.store "f" (.lit 2) (.var "hi")) (.seq (.store "f" (.lit 3) (.var "hj"))
      (.seq (.assign "y" (.var "hy")) (.seq (.assign "p" (.lit 0)) (.seq (.assign "op" (.lit 4)) atScan))))))

theorem hitC_reads : ¬ hitC.reads := by decide
theorem hitC_noWrite : hitC.NoWrite := by decide

theorem hitC_spec (B : ℕ) (X : List ℕ) (y s i j : ℕ) (C : Env → Prop) (hC : Stable C hitC)
    (hL : ListFacts X y) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) (hs : s < B)
    (hi : i < B) (hj : j < B) :
    Spec B (fun τ => C τ ∧ τ.arrs "x" = X ∧ (τ.arrs "f").length = 4 ∧ τ.vars "hy" = y ∧
      τ.vars "hs" = s ∧ τ.vars "hi" = i ∧ τ.vars "hj" = j) hitC
      (fun _ τ' => C τ' ∧ τ'.vars "v" = bv (hit X y s i j)) (70 * X.length + 100) := by
  rintro τ ⟨hCτ, hx, hf, hy, hs', hi', hj'⟩
  obtain ⟨f0, f1, f2, f3, hf4⟩ : ∃ a b c d, τ.arrs "f" = [a, b, c, d] := by
    match h : τ.arrs "f", hf with
    | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩
  set τ1 := τ.setArr "f" 0 4
  set τ2 := τ1.setArr "f" 1 s
  set τ3 := τ2.setArr "f" 2 i
  set τ4 := τ3.setArr "f" 3 j
  have hf5 : τ4.arrs "f" = [4, s, i, j] := by simp [τ4, τ3, τ2, τ1, Env.setArr, hf4]
  set τ5 := ((τ4.setVar "y" y).setVar "p" 0).setVar "op" 4
  obtain ⟨τ6, hr6, hv6⟩ := atScan_spec B X [4, s, i, j] y 0 4 hL (by simp)
    hX (by intro v hv; simp at hv; omega) hXB (by simp; omega) (by omega) τ5
    ⟨by simp [τ5, τ4, τ3, τ2, τ1, Env.setArr, hx], by simp [τ5, hf5], by simp [τ5], by simp [τ5],
      by simp [τ5]⟩
  have hl1 : (τ.arrs "f").length = 4 := hf
  have hyX : y < X.length := by
    have := hL.frPos_le 0 (Nat.zero_le _); have := hL.end_le; omega
  have r1 : Run B (.store "f" (.lit 0) (.lit 4)) τ τ1 3 :=
    (Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) (by omega)).mono (by simp)
  have r2 : Run B (.store "f" (.lit 1) (.var "hs")) τ1 τ2 3 :=
    (Run.store (evalB_lit (by omega)) (evalB_var (by simp [τ1]; omega)) (by simp [τ1]; omega)).mono
      (by simp) |>.congr (by simp [τ2, τ1, hs'])
  have r3 : Run B (.store "f" (.lit 2) (.var "hi")) τ2 τ3 3 :=
    (Run.store (evalB_lit (by omega)) (evalB_var (by simp [τ2, τ1]; omega)) (by simp [τ2, τ1]; omega)).mono
      (by simp) |>.congr (by simp [τ3, τ2, τ1, hi'])
  have r4 : Run B (.store "f" (.lit 3) (.var "hj")) τ3 τ4 3 :=
    (Run.store (evalB_lit (by omega)) (evalB_var (by simp [τ3, τ2, τ1]; omega))
      (by simp [τ3, τ2, τ1]; omega)).mono (by simp) |>.congr (by simp [τ4, τ3, τ2, τ1, hj'])
  have r5 : Run B (.assign "y" (.var "hy")) τ4 (τ4.setVar "y" y) 2 :=
    (Run.assign (evalB_var (by simp [τ4, τ3, τ2, τ1]; omega))).mono (by simp) |>.congr
      (by simp [τ4, τ3, τ2, τ1, hy])
  have r6 : Run B (.assign "p" (.lit 0)) (τ4.setVar "y" y) ((τ4.setVar "y" y).setVar "p" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have r7 : Run B (.assign "op" (.lit 4)) ((τ4.setVar "y" y).setVar "p" 0) τ5 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hrun : Run B hitC τ τ6 (70 * X.length + 100) := by
    unfold hitC
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 hr6))))))).mono
      (by omega)
  refine ⟨τ6, hrun, hC.run hrun hitC_reads hitC_noWrite hCτ, ?_⟩
  rw [hv6]; rfl

end Lax185574Proofs.FarRam
