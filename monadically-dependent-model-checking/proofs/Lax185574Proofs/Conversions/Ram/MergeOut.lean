import Lax185574Proofs.Conversions.Ram.Encode

/-!
Writing a partition held as labels and a graph held as a matrix.

`writeParts` writes the word of the partition whose labels are in the
array `qlab`, in the form `toWord_setoid`. `writeGraph` writes the word
of the graph whose adjacency matrix is `Rm`, in the form `toWord_graph`.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- The test `qlab[w] = r`. -/
def partTest : Cond := .eq (.get "qlab" (.var "w")) (.var "r")

/-- Write the part with least vertex `r` if it has size `k`. -/
def writePart : Com :=
  .ite (.eq (.get "qlab" (.var "r")) (.var "r"))
    (.seq (countRow partTest) (.ite (.eq (.var "d") (.var "k"))
      (.seq (.write (.add (.mul (.lit 2) (.var "k")) (.lit 1)))
        (.seq (.write (.var "k")) (emitRow partTest))) .skip))
    .skip

/-- Write the partition with the labels `qlab`. -/
def writeParts : Com :=
  .seq (countRow (.eq (.get "qlab" (.var "w")) (.var "w"))) (.seq (.write (.var "d"))
    (forUp "k" (.add (.var "n") (.lit 1)) (forUp "r" (.var "n") writePart)))

/-- What `writeParts` reads. -/
structure PartsCtx (n : ℕ) (q : ℕ → ℕ) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hq : Vec τ "qlab" n q

theorem PartsCtx.setVar {n : ℕ} {q : ℕ → ℕ} {τ : Env} (h : PartsCtx n q τ) (x : String)
    (hx : x ≠ "n") (v : ℕ) : PartsCtx n q (τ.setVar x v) :=
  ⟨by simp [Ne.symm hx, h.hn], h.hq.of_eq (by simp)⟩

theorem PartsCtx.setOut {n : ℕ} {q : ℕ → ℕ} {τ : Env} (h : PartsCtx n q τ) (o : List ℕ) :
    PartsCtx n q { τ with out := o } := ⟨h.hn, h.hq.of_eq rfl⟩

theorem evalB_qlab {B n : ℕ} {q : ℕ → ℕ} {τ : Env} (h : PartsCtx n q τ) (hqn : ∀ z < n, q z < n)
    (hnB : n + 1 < B) {x : String} {i : ℕ} (hx : τ.vars x = i) (hi : i < n) :
    (Expr.get "qlab" (.var x)).evalB B τ = some (q i) :=
  h.hq.evalB hx hi (by omega) (by have := hqn i hi; omega)

open Classical in
theorem writePart_run {B n k r : ℕ} {q : ℕ → ℕ} {τ : Env} (hc : PartsCtx n q τ)
    (hqn : ∀ z < n, q z < n) (hB : 2 * n + 3 < B) (hk : τ.vars "k" = k) (hkn : k ≤ n)
    (hr : τ.vars "r" = r) (hrn : r < n) :
    ∃ τ', Run B writePart τ τ' (2 * n * 20 + 40) ∧ PartsCtx n q τ' ∧ τ'.vars "k" = k ∧
      τ'.vars "r" = r ∧
      τ'.out = τ.out ++ (if q r = r ∧ (members n q r).length = k then
        (2 * k + 1) :: k :: elemFrames (members n q r) else []) := by
  have hqr := evalB_qlab (B := B) hc hqn (by omega) hr hrn
  have hrv : (Expr.var "r").evalB B τ = some r := by rw [evalB_var (by omega), hr]
  by_cases hrep : q r = r
  swap
  · refine ⟨τ, (Run.ite_false (by rw [evalB_condEq' hqr hrv]; simp [hrep]) Run.skip).mono
      (by simp), hc, hk, hr, by simp [hrep]⟩
  have hc1 : (Cond.eq (.get "qlab" (.var "r")) (.var "r")).evalB B τ = some true := by
    rw [evalB_condEq' hqr hrv]; simp [hrep]
  -- count the members
  let Ctx : Env → Prop := fun ρ => PartsCtx n q ρ ∧ ρ.vars "k" = k ∧ ρ.vars "r" = r
  have hpt : ∀ ρ j, Ctx ρ → ρ.vars "w" = j → j < n →
      partTest.evalB B ρ = some (decide (q j = r)) := fun ρ j h hw hj => by
    rw [partTest, evalB_condEq' (evalB_qlab h.1 hqn (by omega) hw hj)
      (by rw [evalB_var (by rw [h.2.2]; omega), h.2.2])]
  obtain ⟨τ1, hr1, ⟨hc1', hk1, hr1'⟩, hd1, ho1⟩ := countRow_run (B := B) (c := partTest) Ctx
    (fun j => q j = r) (by omega) (fun ρ h => h.1.hn)
    (fun ρ x h => ⟨h.1.setVar "w" (by decide) x, by simp [h.2.1], by simp [h.2.2]⟩)
    (fun ρ x h => ⟨h.1.setVar "d" (by decide) x, by simp [h.2.1], by simp [h.2.2]⟩)
    hpt ⟨hc, hk, hr⟩
  have hlen := length_below_le n (fun j => q j = r)
  have hdv : (Expr.var "d").evalB B τ1 = some (members n q r).length := by
    rw [evalB_var (by rw [hd1]; omega), hd1]; rfl
  have hkv : (Expr.var "k").evalB B τ1 = some k := by rw [evalB_var (by omega), hk1]
  by_cases hsz : (members n q r).length = k
  swap
  · refine ⟨τ1, (Run.ite_true hc1 (Run.seq hr1 (Run.ite_false (by
      rw [evalB_condEq' hdv hkv]; simp [hsz]) Run.skip))).mono (by simp [partTest]; ring_nf; omega),
      hc1', hk1, hr1', by simp [ho1, hsz]⟩
  set τ1' : Env := { τ1 with out := τ1.out ++ [2 * k + 1] } with hτ1'
  set τ2 : Env := { τ1' with out := τ1'.out ++ [k] } with hτ2
  have hwa : Run B (.write (.add (.mul (.lit 2) (.var "k")) (.lit 1))) τ1 τ1' 6 := by
    refine (Run.write ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_lit_iff, evalB_var_iff, Bop.apply_add, Bop.apply_mul]
    exact ⟨2 * k, 1, ⟨2, k, ⟨rfl, by omega⟩, ⟨hk1.symm, by omega⟩, rfl, by omega⟩, ⟨rfl, by omega⟩,
      rfl, by omega⟩
  have hwb : Run B (.write (.var "k")) τ1' τ2 2 := by
    refine (Run.write ?_).mono (by simp)
    simp [hτ1', hk1]; omega
  obtain ⟨τ3, hr3, ⟨hc3, hk3, hr3'⟩, ho3⟩ := emitRow_run (B := B) (c := partTest) Ctx
    (fun j => q j = r) (by omega) (fun ρ h => h.1.hn)
    (fun ρ x h => ⟨h.1.setVar "w" (by decide) x, by simp [h.2.1], by simp [h.2.2]⟩)
    (fun ρ o h => ⟨h.1.setOut o, h.2.1, h.2.2⟩) hpt (σ := τ2) ⟨hc1'.setOut _, by simp [hτ2, hτ1', hk1], by simp [hτ2, hτ1', hr1']⟩
  refine ⟨τ3, (Run.ite_true hc1 (Run.seq hr1 (Run.ite_true (by
      rw [evalB_condEq' hdv hkv]; simp [hsz]) (Run.seq hwa (Run.seq hwb hr3))))).mono ?_,
      hc3, hk3, hr3', ?_⟩
  · simp [partTest]; ring_nf; omega
  · rw [ho3, hτ2, hτ1']
    simp only [members] at hsz
    simp [ho1, hrep, hsz, members]

open Classical in
/-- **Writing a partition.** -/
theorem writeParts_run {B n : ℕ} {q : ℕ → ℕ} {τ : Env} (hc : PartsCtx n q τ)
    (hqn : ∀ z < n, q z < n) (hB : 2 * n + 3 < B) :
    ∃ τ', Run B writeParts τ τ' (100 * (n + 1) ^ 3) ∧ PartsCtx n q τ' ∧
      τ'.out = τ.out ++ ((below n fun r => q r = r).length :: partsOut n q) := by
  have hrep : ∀ ρ j, PartsCtx n q ρ → ρ.vars "w" = j → j < n →
      (Cond.eq (.get "qlab" (.var "w")) (.var "w")).evalB B ρ = some (decide (q j = j)) :=
    fun ρ j h hw hj => by
      rw [evalB_condEq' (evalB_qlab h hqn (by omega) hw hj)
        (by rw [evalB_var (by rw [hw]; omega), hw])]
  obtain ⟨τ1, hr1, hc1, hd1, ho1⟩ := countRow_run (B := B)
    (c := .eq (.get "qlab" (.var "w")) (.var "w")) (PartsCtx n q) (fun j => q j = j) (by omega)
    (fun ρ h => h.hn) (fun ρ x h => h.setVar "w" (by decide) x)
    (fun ρ x h => h.setVar "d" (by decide) x) hrep hc
  have hlen := length_below_le n (fun j => q j = j)
  set c0 := (below n fun r => q r = r).length
  set τ2 : Env := { τ1 with out := τ1.out ++ [c0] } with hτ2
  have hw : Run B (.write (.var "d")) τ1 τ2 2 :=
    (Run.write (by rw [evalB_var (by rw [hd1]; omega), hd1])).mono (by simp)
  let inner : ℕ → List ℕ := fun k => (List.range n).flatMap fun r =>
    if q r = r ∧ (members n q r).length = k then (2 * k + 1) :: k :: elemFrames (members n q r)
    else []
  let IK : ℕ → Env → Prop := fun k ρ => PartsCtx n q ρ ∧
    ρ.out = τ.out ++ (c0 :: (List.range k).flatMap inner)
  obtain ⟨τ3, hr3, ⟨hc3, ho3⟩, -⟩ :=
    forUp_run (B := B) (i := "k") (e := .add (.var "n") (.lit 1))
      (body := forUp "r" (.var "n") writePart) (N := n + 1) (K := n * (40 * n + 48) + 6) IK
      (by omega)
      (fun k _ ρ hI _ => by
        rw [evalB_bin (evalB_var (by rw [hI.1.hn]; omega)) (evalB_lit (by omega))
          (by simp [hI.1.hn]; omega)]
        simp [hI.1.hn])
      (σ := τ2) ⟨(hc1.setOut _).setVar "k" (by decide) 0, by simp [hτ2, ho1]⟩
      (by
        rintro k hk ρ ⟨hcρ, hoρ⟩ hkk
        let IR : ℕ → Env → Prop := fun r ρ' => PartsCtx n q ρ' ∧ ρ'.vars "k" = k ∧
          ρ'.out = ρ.out ++ (List.range r).flatMap fun r =>
            if q r = r ∧ (members n q r).length = k then
              (2 * k + 1) :: k :: elemFrames (members n q r) else []
        obtain ⟨ρ', hr', ⟨hc', hk', ho'⟩, -⟩ :=
          forUp_run (B := B) (i := "r") (e := .var "n") (body := writePart) (N := n)
            (K := 2 * n * 20 + 40) IR (by omega)
            (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
            (σ := ρ) ⟨hcρ.setVar "r" (by decide) 0, by simp [hkk], by simp⟩
            (by
              rintro r hr ρ1 ⟨hc1, hk1, ho1⟩ hrr
              obtain ⟨ρ2, hr2, hc2, hk2, hr2', ho2⟩ := writePart_run hc1 hqn hB hk1 (by omega) hrr hr
              refine ⟨ρ2, hr2, hr2', hc2.setVar "r" (by decide) _, by simp [hk2], ?_⟩
              simp only [out_setVar, ho2, ho1, List.range_succ, List.flatMap_append,
                List.append_assoc]
              simp)
        refine ⟨ρ', hr'.mono (by simp; ring_nf; omega), hk', hc'.setVar "k" (by decide) _, ?_⟩
        simp only [out_setVar, ho', hoρ, List.range_succ, List.flatMap_append, List.append_assoc]
        simp [inner])
  refine ⟨τ3, (Run.seq hr1 (Run.seq hw hr3)).mono ?_, hc3, ?_⟩
  · simp only [Expr.size, Cond.size]
    ring_nf
    nlinarith [Nat.zero_le n, Nat.zero_le (n * n), Nat.zero_le (n * n * n)]
  · rw [ho3]
    simp only [partsOut, inner, members]

/-- The test `Rm[v, w] = 1`. -/
def rmTest : Cond := .eq (.get "Rm" (rm "v" "w")) (.lit 1)

/-- Write the graph with adjacency matrix `Rm`. -/
def writeGraph : Com :=
  .seq (.write (.var "n")) (forUp "v" (.var "n")
    (.seq (countRow rmTest) (.seq (.write (.var "d")) (emitRow rmTest))))

/-- What `writeGraph` reads. -/
structure GraphCtx (n : ℕ) (N : ℕ → ℕ → Prop) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hR : Mat τ "Rm" n fun v u => ind (N v u)

theorem GraphCtx.setVar {n : ℕ} {N : ℕ → ℕ → Prop} {τ : Env} (h : GraphCtx n N τ) (x : String)
    (hx : x ≠ "n") (v : ℕ) : GraphCtx n N (τ.setVar x v) :=
  ⟨by simp [Ne.symm hx, h.hn], h.hR.of_eq (by simp)⟩

theorem GraphCtx.setOut {n : ℕ} {N : ℕ → ℕ → Prop} {τ : Env} (h : GraphCtx n N τ) (o : List ℕ) :
    GraphCtx n N { τ with out := o } := ⟨h.hn, h.hR.of_eq rfl⟩

open Classical in
/-- **Writing a graph.** -/
theorem writeGraph_run {B n : ℕ} {N : ℕ → ℕ → Prop} {τ : Env} (hc : GraphCtx n N τ)
    (hB : n * n + n + 1 < B) :
    ∃ τ', Run B writeGraph τ τ' (100 * (n + 1) ^ 2) ∧ GraphCtx n N τ' ∧
      τ'.out = τ.out ++ graphWord n N := by
  have hnn : n ≤ n * n := Nat.le_mul_self n
  set τ0 : Env := { τ with out := τ.out ++ [n] } with hτ0
  have hw0 : Run B (.write (.var "n")) τ τ0 2 :=
    (Run.write (by rw [evalB_var (by rw [hc.hn]; omega), hc.hn])).mono (by simp)
  let IV : ℕ → Env → Prop := fun k ρ => GraphCtx n N ρ ∧
    ρ.out = τ.out ++ (n :: (List.range k).flatMap fun v =>
      (below n (N v)).length :: elemFrames (below n (N v)))
  obtain ⟨τ1, hr1, ⟨hc1, ho1⟩, -⟩ :=
    forUp_run (B := B) (i := "v") (e := .var "n")
      (body := .seq (countRow rmTest) (.seq (.write (.var "d")) (emitRow rmTest))) (N := n)
      (K := 50 * n + 30) IV (by omega)
      (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
      (σ := τ0) ⟨(hc.setOut _).setVar "v" (by decide) 0, by simp [hτ0]⟩
      (by
        rintro k hk ρ ⟨hcρ, hoρ⟩ hvk
        let Ctx : Env → Prop := fun ρ' => GraphCtx n N ρ' ∧ ρ'.vars "v" = k
        have ht : ∀ ρ' j, Ctx ρ' → ρ'.vars "w" = j → j < n →
            rmTest.evalB B ρ' = some (decide (N k j)) := fun ρ' j h hw hj => by
          have := h.1.hR.evalB (B := B) h.1.hn h.2 hw hk hj (by omega) (by omega)
            (by have := ind_le_one (N k j); omega)
          rw [rmTest, evalB_condEq' this (evalB_lit (by omega))]
          simp [ind_eq_one]
        obtain ⟨ρ1, hr1, ⟨hc1, hv1⟩, hd1, ho1⟩ := countRow_run (B := B) (c := rmTest) Ctx (N k)
          (by omega) (fun ρ h => h.1.hn) (fun ρ x h => ⟨h.1.setVar "w" (by decide) x, by simp [h.2]⟩)
          (fun ρ x h => ⟨h.1.setVar "d" (by decide) x, by simp [h.2]⟩) ht ⟨hcρ, hvk⟩
        have hlen := length_below_le n (N k)
        set ρ2 : Env := { ρ1 with out := ρ1.out ++ [(below n (N k)).length] } with hρ2
        have hw : Run B (.write (.var "d")) ρ1 ρ2 2 :=
          (Run.write (by rw [evalB_var (by rw [hd1]; omega), hd1])).mono (by simp)
        obtain ⟨ρ3, hr3, ⟨hc3, hv3⟩, ho3⟩ := emitRow_run (B := B) (c := rmTest) Ctx (N k)
          (by omega) (fun ρ h => h.1.hn) (fun ρ x h => ⟨h.1.setVar "w" (by decide) x, by simp [h.2]⟩)
          (fun ρ o h => ⟨h.1.setOut o, h.2⟩) ht (σ := ρ2) ⟨hc1.setOut _, by simp [hρ2, hv1]⟩
        refine ⟨ρ3, (Run.seq hr1 (Run.seq hw hr3)).mono (by simp [rmTest]; ring_nf; omega), hv3,
          hc3.setVar "v" (by decide) _, ?_⟩
        simp only [out_setVar, ho3, hρ2, ho1, hoρ, List.range_succ, List.flatMap_append]
        simp)
  refine ⟨τ1, (Run.seq hw0 hr1).mono ?_, hc1, by rw [ho1]; rfl⟩
  simp only [size_var]
  ring_nf
  nlinarith [Nat.zero_le n, Nat.zero_le (n * n)]

end Lax185574Proofs.Conversions.Ram
