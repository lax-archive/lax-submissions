import Lax185574Proofs.MainRam.ValidAdj
import Lax185574Proofs.MainRam.ValidRead
import Lax185574Proofs.Conversions.Ram.Basic

/-!
The validation program, part three: the checks. Each check clears the
flag `ok` when it fails, and a loop of checks leaves `ok` alone exactly
when all its rounds pass.
-/

namespace Lax185574Proofs.MainRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Classical

/-! ### Equality as a value -/

/-- `1` if the two values are equal, else `0`. -/
def eqX (e f : Expr) : Expr := .sub (.sub (.lit 1) (.sub e f)) (.sub f e)

@[simp] theorem size_eqX (e f : Expr) : (eqX e f).size = 2 * e.size + 2 * f.size + 5 := by
  simp [eqX]; ring

theorem evalB_eqX {B : ℕ} {σ : Env} {e f : Expr} {m n : ℕ} (he : e.evalB B σ = some m)
    (hf : f.evalB B σ = some n) (hB : 1 < B) (hm : m < B) (hn : n < B) :
    (eqX e f).evalB B σ = some (ind (m = n)) := by
  have h1 := evalB_bin (op := .sub) he hf (by simp; omega)
  have h2 := evalB_bin (op := .sub) hf he (by simp; omega)
  have h3 := evalB_bin (op := .sub) (evalB_lit (n := 1) (σ := σ) hB) h1 (by simp; omega)
  have h4 := evalB_bin (op := .sub) h3 h2 (by simp; omega)
  unfold eqX
  rw [h4]
  unfold ind
  by_cases h : m = n
  · simp [h]
  · simp [h]; omega

/-! ### One check and a loop of checks -/

/-- Clear `ok` unless the condition holds. -/
def chkIf (c : Cond) : Com := .ite c .skip (.assign "ok" (.lit 0))

theorem chkIf_run {B : ℕ} {τ : Env} {c : Cond} {P : Prop} (hB : 0 < B)
    (hc : ∃ bv, c.evalB B τ = some bv ∧ (bv = true ↔ P)) :
    ∃ τ', Run B (chkIf c) τ τ' (c.size + 4) ∧ τ'.vars "ok" = (if P then τ.vars "ok" else 0) ∧
      (∀ z, z ≠ "ok" → τ'.vars z = τ.vars z) ∧ τ'.arrs = τ.arrs ∧ τ'.inp = τ.inp ∧
      τ'.out = τ.out := by
  obtain ⟨bv, hbv, hiff⟩ := hc
  cases bv with
  | true =>
      have hP : P := hiff.1 rfl
      exact ⟨τ, (Run.ite_true hbv Run.skip).mono (by omega), by simp [hP], fun _ _ => rfl, rfl,
        rfl, rfl⟩
  | false =>
      have hP : ¬ P := fun h => by have := hiff.2 h; cases this
      exact ⟨τ.setVar "ok" 0, (Run.ite_false hbv (Run.assign (evalB_lit hB))).mono
        (by simp only [Expr.size]; omega),
        by simp [hP], fun z hz => by simp [hz], rfl, rfl, rfl⟩

/-- **A loop of checks.** -/
theorem chk_run {B N K : ℕ} {i : String} {e : Expr} {body : Com} (Ctx : Env → Prop)
    (p : ℕ → Prop) (hN : N < B) (hi : i ≠ "ok")
    (he : ∀ τ, Ctx τ → e.evalB B τ = some N) (hCi : ∀ τ x, Ctx τ → Ctx (τ.setVar i x))
    (hbody : ∀ k < N, ∀ τ, Ctx τ → τ.vars i = k → ∃ τ', Run B body τ τ' K ∧ Ctx τ' ∧
      τ'.vars i = k ∧ τ'.vars "ok" = (if p k then τ.vars "ok" else 0))
    {σ : Env} (hσ : Ctx σ) :
    ∃ σ', Run B (forUp i e body) σ σ' (N * (K + e.size + 7) + e.size + 5) ∧ Ctx σ' ∧
      σ'.vars "ok" = if (∀ k < N, p k) then σ.vars "ok" else 0 := by
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧
    τ.vars "ok" = if (∀ k' < k, p k') then σ.vars "ok" else 0
  obtain ⟨σ', hr, ⟨hC, hok⟩, -⟩ := forUp_run (B := B) (i := i) (e := e) (body := body) (N := N)
    (K := K) I hN (fun k _ τ hI _ => he τ hI.1)
    ⟨hCi _ _ hσ, by simp [hi.symm]⟩
    (by
      rintro k hk τ ⟨hC, hok⟩ hik
      obtain ⟨τ', hr, hC', hik', hok'⟩ := hbody k hk τ hC hik
      refine ⟨τ', hr, hik', hCi _ _ hC', ?_⟩
      simp only [vars_setVar, show ("ok" : String) = i ↔ False from ⟨fun h => hi h.symm,
        False.elim⟩, if_false, hok', hok]
      by_cases hpk : p k
      · simp only [hpk, if_true]
        congr 1; apply propext
        constructor
        · intro h k' hk'; rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with h' | rfl
          · exact h k' h'
          · exact hpk
        · intro h k' hk'; exact h k' (by omega)
      · simp only [hpk, if_false]
        rw [if_neg (fun h => hpk (h k (by omega)))])
  exact ⟨σ', hr, hC, hok⟩

/-! ### The data read by the first phases -/

/-- The data of the validation, fixed after reading. -/
structure VData where
  n : ℕ
  L : ℕ
  E : ℕ
  nF : ℕ
  m : ℕ
  y : List ℕ
  ofv : List ℕ
  tgv : List ℕ
  φw : List ℕ
  Av : List ℕ

/-- The environment holds the data. -/
def VD (d : VData) (τ : Env) : Prop :=
  τ.vars "n" = d.n ∧ τ.vars "L" = d.L ∧ τ.vars "E" = d.E ∧ τ.vars "nF" = d.nF ∧
    τ.vars "m" = d.m ∧ τ.arrs "Y" = d.y ∧ τ.arrs "of" = d.ofv ∧ τ.arrs "tg" = d.tgv ∧
    τ.arrs "F" = d.φw ∧ τ.arrs "A" = d.Av

theorem VD.setVar {d : VData} {τ : Env} (h : VD d τ) {x : String} (v : ℕ)
    (hx : x ∉ ["n", "L", "E", "nF", "m"]) : VD d (τ.setVar x v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, a6, a7, a8, a9, a10⟩ <;>
    simp [Env.setVar, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, *]

theorem VD.setArr {d : VData} {τ : Env} (h : VD d τ) {a : String} (i v : ℕ)
    (ha : a ∉ ["Y", "of", "tg", "F", "A"]) : VD d (τ.setArr a i v) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
  obtain ⟨h1, h2, h3, h4, h5⟩ := ha
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := h
  refine ⟨a1, a2, a3, a4, a5, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Env.setArr, Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, *]

/-! ### The shape of the script word -/

/-- The index of the opcode of step `t`. -/
def opIdx : Expr := .add (.add (.var "n") (.lit 2)) (.mul (.lit 3) (.var "t"))

/-- `ok := 1` exactly when the word has room for its header, starts with
`n`, and has the length its number of steps demands. Also `m` is that
number of steps. -/
def parsePh : Com :=
  .seq (.assign "ok" (.lit 0)) (.seq (.assign "m" (.lit 0))
    (.ite (.lt (.var "L") (.add (.var "n") (.lit 2))) .skip
      (.seq (.assign "m" (.get "Y" (.add (.var "n") (.lit 1))))
        (.ite (.eq (.get "Y" (.lit 0)) (.var "n"))
          (.ite (.eq (.var "L") (.add (.add (.var "n") (.lit 2)) (.mul (.lit 3) (.var "m"))))
            (.assign "ok" (.lit 1)) .skip) .skip))))

/-- The shape condition of `parsePh`. -/
def Shape (n : ℕ) (y : List ℕ) : Prop :=
  y.getD 0 0 = n ∧ y.length = n + 2 + 3 * numSteps n y

theorem parseOK_iff (n : ℕ) (y : List ℕ) :
    ParseOK n y ↔ Shape n y ∧ ∀ t < numSteps n y, y.getD (n + 2 + 3 * t) 0 < 3 := by
  unfold ParseOK Shape
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, fun t ht => by have := h3 t ht; omega⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, fun t ht => by have := h3 t ht; omega⟩

theorem getY {y : List ℕ} {i : ℕ} (h : i < y.length) : y[i]? = some (y.getD i 0) := by
  rw [List.getElem?_eq_getElem h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem parsePh_run {B Λ : ℕ} {τ : Env} {n : ℕ} {y : List ℕ} (hn : τ.vars "n" = n)
    (hL : τ.vars "L" = y.length) (hY : τ.arrs "Y" = y) (hyΛ : ∀ a ∈ y, a ≤ Λ)
    (hlΛ : y.length ≤ Λ) (hnΛ : n ≤ Λ) (hB : 4 * Λ + 8 < B) :
    ∃ τ', Run B parsePh τ τ' 40 ∧ τ'.vars "ok" = ind (Shape n y) ∧
      (Shape n y → τ'.vars "m" = numSteps n y) ∧
      (∀ z, z ≠ "ok" → z ≠ "m" → τ'.vars z = τ.vars z) ∧ τ'.arrs = τ.arrs ∧
      τ'.inp = τ.inp ∧ τ'.out = τ.out := by
  have hgetΛ : ∀ i, y.getD i 0 ≤ Λ := by
    intro i
    rcases Nat.lt_or_ge i y.length with h | h
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact hyΛ _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]; omega
  obtain ⟨τ1, r1, a1, f1, ar1, i1, o1⟩ := assign_step (B := B) (σ := τ) "ok" (e := .lit 0)
    (evalB_lit (by omega))
  obtain ⟨τ2, r2, a2, f2, ar2, i2, o2⟩ := assign_step (B := B) (σ := τ1) "m" (e := .lit 0)
    (evalB_lit (by omega))
  have hn2 : τ2.vars "n" = n := by rw [f2 _ (by decide), f1 _ (by decide), hn]
  have hL2 : τ2.vars "L" = y.length := by rw [f2 _ (by decide), f1 _ (by decide), hL]
  have hok2 : τ2.vars "ok" = 0 := by rw [f2 _ (by decide), a1]
  have hY2 : τ2.arrs "Y" = y := by rw [ar2, ar1, hY]
  have hfr2 : ∀ z, z ≠ "ok" → z ≠ "m" → τ2.vars z = τ.vars z := fun z h1 h2 => by
    rw [f2 z h2, f1 z h1]
  have hc1 := evalB_condLt (B := B) (σ := τ2) (e := .var "L") (f := .add (.var "n") (.lit 2))
    (evalB_var (by rw [hL2]; omega)) (evalB_bin (evalB_var (by rw [hn2]; omega))
      (evalB_lit (by omega)) (by simp [hn2]; omega))
  simp only [hL2, hn2, Bop.apply_add] at hc1
  by_cases hshort : y.length < n + 2
  · have hS : ¬ Shape n y := fun h => by have := h.2; omega
    refine ⟨τ2, (r1.seq (r2.seq (Run.ite_true (by rw [hc1, decide_eq_true hshort]) Run.skip))).mono
      (by simp), by rw [hok2, ind, if_neg hS], fun h => absurd h hS, hfr2, by rw [ar2, ar1],
      by rw [i2, i1], by rw [o2, o1]⟩
  · have hidx : (Expr.add (.var "n") (.lit 1)).evalB B τ2 = some (n + 1) := by
      have := evalB_bin (op := .add) (evalB_var (B := B) (σ := τ2) (x := "n") (by rw [hn2]; omega))
        (evalB_lit (n := 1) (σ := τ2) (by omega)) (by simp [hn2]; omega)
      simpa [hn2] using this
    have hm := evalB_get (B := B) (σ := τ2) (a := "Y") (i := .add (.var "n") (.lit 1))
      (k := n + 1) hidx (by rw [hY2]; exact getY (by omega)) (by have := hgetΛ (n + 1); omega)
    obtain ⟨τ3, r3, a3, f3, ar3, i3, o3⟩ := assign_step (B := B) (σ := τ2) "m" hm
    have hn3 : τ3.vars "n" = n := by rw [f3 _ (by decide), hn2]
    have hL3 : τ3.vars "L" = y.length := by rw [f3 _ (by decide), hL2]
    have hY3 : τ3.arrs "Y" = y := by rw [ar3, hY2]
    have hok3 : τ3.vars "ok" = 0 := by rw [f3 _ (by decide), hok2]
    have hmΛ := hgetΛ (n + 1)
    have hc2 := evalB_condEq' (B := B) (σ := τ3) (e := .get "Y" (.lit 0)) (f := .var "n")
      (evalB_get (k := 0) (evalB_lit (by omega)) (by rw [hY3]; exact getY (by omega))
        (by have := hgetΛ 0; omega)) (evalB_var (by rw [hn3]; omega))
    rw [hn3] at hc2
    have hfr3 : ∀ z, z ≠ "ok" → z ≠ "m" → τ3.vars z = τ.vars z := fun z h1 h2 => by
      rw [f3 z h2, hfr2 z h1 h2]
    by_cases h0 : y.getD 0 0 = n
    · have e1 : (Expr.add (.var "n") (.lit 2)).evalB B τ3 = some (n + 2) := by
        have := evalB_bin (op := .add) (evalB_var (B := B) (σ := τ3) (x := "n") (by rw [hn3]; omega))
          (evalB_lit (n := 2) (σ := τ3) (by omega)) (by simp [hn3]; omega)
        simpa [hn3] using this
      have e2 : (Expr.mul (.lit 3) (.var "m")).evalB B τ3 = some (3 * y.getD (n + 1) 0) := by
        have := evalB_bin (op := .mul) (evalB_lit (n := 3) (B := B) (σ := τ3) (by omega))
          (evalB_var (x := "m") (by rw [a3]; omega)) (by show 3 * τ3.vars "m" < B; rw [a3]; omega)
        rw [a3] at this; exact this
      have e3 := evalB_bin (op := .add) e1 e2 (by show n + 2 + 3 * y.getD (n + 1) 0 < B; omega)
      have hc3 := evalB_condEq' (B := B) (σ := τ3) (e := .var "L") (evalB_var (by rw [hL3]; omega)) e3
      simp only [hL3, Bop.apply_add] at hc3
      by_cases hl : y.length = n + 2 + 3 * y.getD (n + 1) 0
      · have hS : Shape n y := ⟨h0, hl⟩
        obtain ⟨τ4, r4, a4, f4, ar4, i4, o4⟩ := assign_step (B := B) (σ := τ3) "ok" (e := .lit 1)
          (evalB_lit (by omega))
        refine ⟨τ4, (r1.seq (r2.seq (Run.ite_false (by rw [hc1, decide_eq_false hshort])
          (r3.seq (Run.ite_true (by rw [hc2, decide_eq_true h0])
            (Run.ite_true (by rw [hc3, decide_eq_true hl]) r4)))))).mono (by simp),
          by rw [a4, ind, if_pos hS], fun _ => by rw [f4 _ (by decide), a3]; rfl,
          fun z h1 h2 => by rw [f4 z h1, hfr3 z h1 h2], by rw [ar4, ar3, ar2, ar1],
          by rw [i4, i3, i2, i1], by rw [o4, o3, o2, o1]⟩
      · have hS : ¬ Shape n y := fun h => hl (by have := h.2; unfold numSteps at this; omega)
        refine ⟨τ3, (r1.seq (r2.seq (Run.ite_false (by rw [hc1, decide_eq_false hshort])
          (r3.seq (Run.ite_true (by rw [hc2, decide_eq_true h0])
            (Run.ite_false (by rw [hc3, decide_eq_false hl]) Run.skip)))))).mono (by simp),
          by rw [hok3, ind, if_neg hS], fun h => absurd h hS, hfr3, by rw [ar3, ar2, ar1],
          by rw [i3, i2, i1], by rw [o3, o2, o1]⟩
    · have hS : ¬ Shape n y := fun h => h0 h.1
      refine ⟨τ3, (r1.seq (r2.seq (Run.ite_false (by rw [hc1, decide_eq_false hshort])
        (r3.seq (Run.ite_false (by rw [hc2, decide_eq_false h0]) Run.skip))))).mono (by simp),
        by rw [hok3, ind, if_neg hS], fun h => absurd h hS, hfr3, by rw [ar3, ar2, ar1],
        by rw [i3, i2, i1], by rw [o3, o2, o1]⟩

end Lax185574Proofs.MainRam
