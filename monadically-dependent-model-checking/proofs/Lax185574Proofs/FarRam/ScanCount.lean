import Lax185574Proofs.FarRam.ScanEq


/-!
The two counts of one entry of the scatter type: `inNC` tests whether a
far extension has the tree of the entry, `cntC` counts the blocks met by
the extensions with this tree.
-/

namespace Lax185574Proofs.FarRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.EvalRam
open Lax185574.WordEncoding

theorem setVar_setVar (σ : Env) (x : String) (a b : ℕ) : (σ.setVar x a).setVar x b = σ.setVar x b := by
  cases σ; simp only [Env.setVar, Env.mk.injEq, and_true]; funext y; split_ifs <;> rfl

/-- `x := 0; if c₁ then if c₂ then x := 1`. -/
def andTest (x : String) (c₁ c₂ : Cond) : Com :=
  .seq (.assign x (.lit 0)) (.ite c₁ (.ite c₂ (.assign x (.lit 1)) .skip) .skip)

theorem andTest_run {B : ℕ} {x : String} {c₁ c₂ : Cond} {σ : Env} {b₁ b₂ : Bool}
    (h₁ : c₁.evalB B (σ.setVar x 0) = some b₁) (h₂ : c₂.evalB B (σ.setVar x 0) = some b₂) (hB : 1 < B) :
    Run B (andTest x c₁ c₂) σ (σ.setVar x (bv (b₁ && b₂))) (c₁.size + c₂.size + 8) := by
  unfold andTest
  cases b₁
  · refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.ite_false h₁ Run.skip)).mono ?_ |>.congr
      (by simp)
    simp; omega
  · cases b₂
    · refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.ite_true h₁ (Run.ite_false h₂ Run.skip))).mono
        ?_ |>.congr (by simp)
      simp; omega
    · refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.ite_true h₁ (Run.ite_true h₂
        (Run.assign (evalB_lit hB))))).mono ?_ |>.congr (by simp [setVar_setVar])
      simp; omega

theorem evalB_bit {B : ℕ} {σ : Env} {A : String} {ie : Expr} {k : ℕ} {b : Bool}
    (hi : ie.evalB B σ = some k) (hA : (σ.arrs A)[k]? = some (bv b)) (hB : 1 < B) :
    (Cond.eq (.get A ie) (.lit 1)).evalB B σ = some b := by
  rw [evalB_condEq (m := bv b) (n := 1) ?_ (evalB_lit hB)]
  · cases b <;> rfl
  · simp only [evalB_get_iff]; exact ⟨k, hi, hA, by have := bv_le b; omega⟩

/-- The facts the tests of an entry read. -/
def TestCtx (X : List ℕ) (W : List (List ℕ)) (nS R r ℓ s i : ℕ) (τ : Env) : Prop :=
  ScanFix W nS R τ ∧ EqAt W nS i R τ ∧ Rows X r ℓ R τ ∧ BtAt X ℓ s ℓ τ ∧ τ.vars "hl" = ℓ

theorem stable_testCtx {c : Com} (X : List ℕ) (W : List (List ℕ)) (nS R r ℓ s i : ℕ)
    (ha : ∀ a ∈ ["a", "st", "ln", "eqa", "mt", "far", "bt"], a ∉ c.warrs)
    (hv : ∀ z ∈ ["ns", "nR", "hl"], z ∉ c.wvars) : Stable (TestCtx X W nS R r ℓ s i) c :=
  fun τ τ' h1 h2 h3 h4 h5 h => ⟨stable_scanFix W nS R (ha "a" (by simp)) (ha "st" (by simp))
    (ha "ln" (by simp)) (hv "ns" (by simp)) (hv "nR" (by simp)) τ τ' h1 h2 h3 h4 h5 h.1,
    by rw [EqAt, h2 "eqa" (ha "eqa" (by simp))]; exact h.2.1,
    stable_rows X r ℓ R (ha "mt" (by simp)) (ha "far" (by simp)) τ τ' h1 h2 h3 h4 h5 h.2.2.1,
    stable_btAt X ℓ s ℓ (ha "bt" (by simp)) τ τ' h1 h2 h3 h4 h5 h.2.2.2.1,
    by rw [h1 "hl" (hv "hl" (by simp))]; exact h.2.2.2.2⟩

theorem ans_length {W : List (List ℕ)} {nS R : ℕ} (h : W.length = nS + R) : (W.drop nS).length = R := by
  simp [h]

def inNTest : Com :=
  andTest "zx" (.eq (.get "eqa" (.var "zu")) (.lit 1)) (.eq (.get "far" (.var "zu")) (.lit 1))

def inNC : Com := .seq (.assign "zn" (.lit 0)) (anyLoop "zu" "nR" "zn" "zx" inNTest)

theorem inNC_spec (B : ℕ) (X : List ℕ) (W : List (List ℕ)) (nS R r ℓ s i : ℕ) (C : Env → Prop)
    (hC : Stable C inNC) (hRB : R + 2 < B) :
    Spec B (fun τ => C τ ∧ TestCtx X W nS R r ℓ s i τ) inNC
      (fun _ τ' => C τ' ∧ TestCtx X W nS R r ℓ s i τ' ∧
        τ'.vars "zn" = bv (inNW X (W.drop nS) r ℓ (nuPart (wd W i)))) (R * 40 + 10) := by
  rintro σ ⟨hCσ, hT⟩
  have hS : Stable (fun ρ => C ρ ∧ TestCtx X W nS R r ℓ s i ρ) inNC :=
    hC.and (stable_testCtx X W nS R r ℓ s i (by decide) (by decide))
  obtain ⟨σ', hr, hC', hzn, -⟩ := anyLoop_run (B := B) (i := "zu") (n := "nR") (flag := "zn") (v := "zx")
    (body := inNTest) (fun ρ => C ρ ∧ TestCtx X W nS R r ℓ s i ρ)
    (fun e => ((W.drop nS).getD e [] == nuPart (wd W i)) && farW X r ℓ e) R 20 (by omega)
    (by decide) (by decide) (by decide) (fun ρ x h => hS.setVar (by decide) ρ x h)
    (fun ρ x h => hS.setVar (by decide) ρ x h)
    (fun c hc ρ ⟨hCρ, hzu, hnR, _⟩ => by
      have hzuE : (Expr.var "zu").evalB B (ρ.setVar "zx" 0) = some c := by
        simp only [evalB_var_iff]; simp [hzu]; omega
      have h1 := evalB_bit (A := "eqa") hzuE (by simpa using hCρ.2.2.1 c hc) (by omega)
      have h2 := evalB_bit (A := "far") hzuE (by simpa using hCρ.2.2.2.1.2 c hc) (by omega)
      have hr := andTest_run (x := "zx") h1 h2 (by omega)
      refine ⟨_, hr.mono (by simp), hS.setVar (by decide) _ _ hCρ, by simp [hzu], by simp [hnR],
        by simp, by simp⟩)
    (σ.setVar "zn" 0) ⟨hS.setVar (by decide) _ _ ⟨hCσ, hT⟩, by simpa using hT.1.2.2.1, by simp⟩
  refine ⟨σ', (Run.seq (Run.assign (evalB_lit (by omega))) hr).mono (by simp; omega), hC'.1, hC'.2, ?_⟩
  rw [hzn, inNW, ans_length hT.1.2.2.2.1]

def mbTest : Com :=
  andTest "zx" (.eq (.get "mt" (.add (.mul (.var "zu") (.var "hl")) (.var "zw"))) (.lit 1))
    (.eq (.get "bt" (.var "zw")) (.var "zbb"))

def blkTest : Com :=
  .seq (.assign "zy" (.lit 0)) (.ite (.eq (.get "eqa" (.var "zu")) (.lit 1))
    (.seq (.assign "zp" (.lit 0)) (.seq (anyLoop "zw" "hl" "zp" "zx" mbTest) (.assign "zy" (.var "zp"))))
    .skip)

def cntBody : Com :=
  .seq (.assign "zq" (.lit 0)) (.seq (anyLoop "zu" "nR" "zq" "zy" blkTest)
    (.assign "zk" (.add (.var "zk") (.var "zq"))))

def cntC : Com := .seq (.assign "zk" (.lit 0)) (forUp "zbb" (.var "hl") cntBody)

theorem length_filter_range_succ (f : ℕ → Bool) (b : ℕ) :
    ((List.range (b + 1)).filter f).length = ((List.range b).filter f).length + bv (f b) := by
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : f b <;> simp [bv, h]

def mbCost : ℕ := 30

def blkCost (ℓ : ℕ) : ℕ := ℓ * (mbCost + 20) + 20

def cntCost (ℓ R : ℕ) : ℕ := ℓ * (R * (blkCost ℓ + 20) + 30) + 10

theorem blkTest_spec (B : ℕ) (X : List ℕ) (W : List (List ℕ)) (nS R r ℓ s i e b : ℕ) (C : Env → Prop)
    (hC : Stable C blkTest) (he : e < R) (hb : b < B) (hRB : R * ℓ + ℓ + 2 < B) (hRB' : R + 2 < B) :
    Spec B (fun τ => C τ ∧ TestCtx X W nS R r ℓ s i τ ∧ τ.vars "zu" = e ∧ τ.vars "zbb" = b) blkTest
      (fun _ τ' => C τ' ∧ TestCtx X W nS R r ℓ s i τ' ∧ τ'.vars "zu" = e ∧ τ'.vars "zbb" = b ∧
        τ'.vars "zy" = bv (((W.drop nS).getD e [] == nuPart (wd W i)) &&
          (List.range ℓ).any fun j => mtW X r ℓ e j && (canonW X s ℓ j == b))) (blkCost ℓ) := by
  rintro σ ⟨hCσ, hT, hzu, hzb⟩
  let D : Env → Prop := fun ρ => C ρ ∧ TestCtx X W nS R r ℓ s i ρ ∧ ρ.vars "zu" = e ∧ ρ.vars "zbb" = b
  have hS : Stable D blkTest := hC.and ((stable_testCtx X W nS R r ℓ s i (by decide) (by decide)).and
    ((stable_var "zu" e (by decide)).and (stable_var "zbb" b (by decide))))
  have hD0 : D (σ.setVar "zy" 0) := hS.setVar (by decide) _ _ ⟨hCσ, hT, hzu, hzb⟩
  have hzuE : (Expr.var "zu").evalB B (σ.setVar "zy" 0) = some e := by
    simp only [evalB_var_iff]; simp [hzu]; omega
  have hc : (Cond.eq (.get "eqa" (.var "zu")) (.lit 1)).evalB B (σ.setVar "zy" 0) =
      some ((W.drop nS).getD e [] == nuPart (wd W i)) :=
    evalB_bit (A := "eqa") hzuE (by rw [arrs_setVar]; exact hT.2.1 e he) (by omega)
  have hRe : e * ℓ + ℓ ≤ R * ℓ := by
    have := Nat.mul_le_mul_right ℓ (show e + 1 ≤ R by omega); rw [Nat.add_mul, one_mul] at this; exact this
  by_cases heq : ((W.drop nS).getD e [] == nuPart (wd W i)) = true
  · set ρ0 := (σ.setVar "zy" 0).setVar "zp" 0
    obtain ⟨ρ1, hr1, hD1, hzp1, -⟩ := anyLoop_run (B := B) (i := "zw") (n := "hl") (flag := "zp") (v := "zx")
      (body := mbTest) D (fun j => mtW X r ℓ e j && (canonW X s ℓ j == b)) ℓ (mbCost) (by omega)
      (by decide) (by decide) (by decide) (fun ρ x h => hS.setVar (by decide) ρ x h)
      (fun ρ x h => hS.setVar (by decide) ρ x h)
      (fun j hj ρ ⟨hDρ, hzw, hhl, _⟩ => by
        have hTρ := hDρ.2.1
        have hidx : (Expr.add (.mul (.var "zu") (.var "hl")) (.var "zw")).evalB B (ρ.setVar "zx" 0) =
            some (e * ℓ + j) := by
          simp only [evalB_bin_iff, evalB_var_iff, vars_setVar]
          have hm : e * ℓ ≤ R * ℓ := Nat.mul_le_mul_right _ he.le
          have heB : e < B := by omega
          exact ⟨e * ℓ, j, ⟨e, ℓ, ⟨by simp [hDρ.2.2.1], by simp [hDρ.2.2.1]; omega⟩,
            ⟨by simp [hhl], by simp [hhl]; omega⟩, rfl, by omega⟩, ⟨by simp [hzw], by simp [hzw]; omega⟩,
            rfl, by omega⟩
        have h1 := evalB_bit (A := "mt") hidx (by simpa using hTρ.2.2.1.1 e he j hj) (by omega)
        have hbt := hTρ.2.2.2.1.2 j hj
        have hcl := canonW_lt X s ℓ j hj
        have h2 : (Cond.eq (.get "bt" (.var "zw")) (.var "zbb")).evalB B (ρ.setVar "zx" 0) =
            some (canonW X s ℓ j == b) := by
          refine evalB_condEq ?_ ?_
          · simp only [evalB_get_iff, evalB_var_iff]
            exact ⟨j, ⟨by simp [hzw], by simp [hzw]; omega⟩, by simpa using hbt, by omega⟩
          · simp only [evalB_var_iff]; simp [hDρ.2.2.2]; omega
        have hr := andTest_run (x := "zx") h1 h2 (by omega)
        refine ⟨_, hr.mono (by simp [mbCost]), hS.setVar (by decide) _ _ hDρ, by simp [hzw], by simp [hhl],
          by simp, by simp⟩)
      ρ0 ⟨hS.setVar (by decide) _ _ hD0, by simpa [ρ0] using hT.2.2.2.2, by simp [ρ0]⟩
    have hzpB : ρ1.vars "zp" ≤ 1 := by rw [hzp1]; exact bv_le _
    refine ⟨ρ1.setVar "zy" (ρ1.vars "zp"), ?_, ?_⟩
    · unfold blkTest
      refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.ite_true (by rw [hc, heq])
        (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq hr1 (Run.assign (v := ρ1.vars "zp")
          (evalB_var (by omega))))))).mono ?_
      simp [blkCost, mbCost]; nlinarith
    · obtain ⟨hC1, hT1, hzu1, hzb1⟩ := hS.setVar (z := "zy") (by decide) _ (ρ1.vars "zp") hD1
      exact ⟨hC1, hT1, hzu1, hzb1, by simp only [vars_setVar, if_true, hzp1, heq, Bool.true_and]⟩
  · have heq' : ((W.drop nS).getD e [] == nuPart (wd W i)) = false := by simpa using heq
    refine ⟨σ.setVar "zy" 0, ?_, hD0.1, hD0.2.1, hD0.2.2.1, hD0.2.2.2,
      by simp only [vars_setVar, if_true, heq', Bool.false_and]; rfl⟩
    unfold blkTest
    refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.ite_false (by rw [hc, heq']) Run.skip)).mono ?_
    simp [blkCost]

theorem cntC_spec (B : ℕ) (X : List ℕ) (W : List (List ℕ)) (nS R r ℓ s i : ℕ) (C : Env → Prop)
    (hC : Stable C cntC) (hRB : R * ℓ + ℓ + 2 < B) (hRB' : R + 2 < B) :
    Spec B (fun τ => C τ ∧ TestCtx X W nS R r ℓ s i τ) cntC
      (fun _ τ' => C τ' ∧ TestCtx X W nS R r ℓ s i τ' ∧
        τ'.vars "zk" = cntW X (W.drop nS) r ℓ (canonW X s ℓ) (nuPart (wd W i))) (cntCost ℓ R) := by
  rintro σ ⟨hCσ, hT⟩
  let D : Env → Prop := fun ρ => C ρ ∧ TestCtx X W nS R r ℓ s i ρ
  have hS : Stable D cntC := hC.and (stable_testCtx X W nS R r ℓ s i (by decide) (by decide))
  have hAl := ans_length hT.1.2.2.2.1
  set f := blkW X (W.drop nS) r ℓ (canonW X s ℓ) (nuPart (wd W i)) with hf
  obtain ⟨σ', hr, ⟨hD', hzk'⟩, -⟩ := forUp_run (B := B) (i := "zbb") (e := .var "hl") (body := cntBody)
    (N := ℓ) (K := R * (blkCost ℓ + 20) + 20)
    (fun b ρ => D ρ ∧ ρ.vars "zk" = ((List.range b).filter f).length) (σ := σ.setVar "zk" 0) (by omega)
    (fun b _ ρ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.1.2.2.2.2.2.symm, by rw [hI.1.2.2.2.2.2]; omega⟩)
    ⟨hS.setVar (by decide) _ _ (hS.setVar (by decide) _ _ ⟨hCσ, hT⟩), by simp⟩
    (fun b hb ρ ⟨hDρ, hzk⟩ hzb => by
      have hS2 : Stable (fun ρ' => D ρ' ∧ ρ'.vars "zbb" = b ∧ ρ'.vars "zk" = ρ.vars "zk") blkTest :=
        (hS.mono (by decide) (by decide)).and ((stable_var "zbb" b (by decide)).and
          (stable_var "zk" _ (by decide)))
      have hset : ∀ z, z ∈ cntBody.wvars → z ≠ "zbb" → z ≠ "zk" → ∀ ρ' x,
          (D ρ' ∧ ρ'.vars "zbb" = b ∧ ρ'.vars "zk" = ρ.vars "zk") →
          (D (ρ'.setVar z x) ∧ (ρ'.setVar z x).vars "zbb" = b ∧ (ρ'.setVar z x).vars "zk" = ρ.vars "zk") :=
        fun z hz h1 h2 ρ' x h => ⟨hS.setVar (by simp [cntC, forUp, Com.wvars] at hz ⊢; tauto) ρ' x h.1,
          by simp [Ne.symm h1, h.2.1], by simp [Ne.symm h2, h.2.2]⟩
      obtain ⟨ρ1, hr1, ⟨hD1, hzb1, hzk1⟩, hzq1, hnR1⟩ := anyLoop_run (B := B) (i := "zu") (n := "nR")
        (flag := "zq") (v := "zy") (body := blkTest)
        (fun ρ' => D ρ' ∧ ρ'.vars "zbb" = b ∧ ρ'.vars "zk" = ρ.vars "zk")
        (fun e => ((W.drop nS).getD e [] == nuPart (wd W i)) &&
          (List.range ℓ).any fun j => mtW X r ℓ e j && (canonW X s ℓ j == b)) R (blkCost ℓ) (by omega)
        (by decide) (by decide) (by decide) (hset "zu" (by decide) (by decide) (by decide))
        (hset "zq" (by decide) (by decide) (by decide))
        (fun e he ρ' ⟨⟨hD', hzb', hzk'⟩, hzu', hnR', _⟩ => by
          have hS3 : Stable (fun ρ'' => (D ρ'' ∧ ρ''.vars "zbb" = b ∧ ρ''.vars "zk" = ρ.vars "zk") ∧
              ρ''.vars "nR" = R ∧ ρ''.vars "zq" = ρ'.vars "zq") blkTest :=
            hS2.and ((stable_var "nR" R (by decide)).and (stable_var "zq" _ (by decide)))
          obtain ⟨ρ'', hr'', ⟨hD'', hnR'', hzq''⟩, hT'', hzu'', -, hzy''⟩ := blkTest_spec B X W nS R r ℓ s i e b _ hS3 he
            (by omega) hRB hRB' ρ' ⟨⟨⟨hD', hzb', hzk'⟩, hnR', rfl⟩, hD'.2, hzu', hzb'⟩
          exact ⟨ρ'', hr'', hD'', hzu'', hnR'', hzq'', hzy''⟩)
        (ρ.setVar "zq" 0) ⟨hset "zq" (by decide) (by decide) (by decide) _ _ ⟨hDρ, hzb, rfl⟩,
          by simpa using hDρ.2.1.2.2.1, by simp⟩
      have hzqB : ρ1.vars "zq" ≤ 1 := by rw [hzq1]; exact bv_le _
      have hlen : ((List.range b).filter f).length ≤ b := by
        have := List.length_filter_le f (List.range b); simpa using this
      refine ⟨ρ1.setVar "zk" (ρ1.vars "zk" + ρ1.vars "zq"), ?_, by simp [hzb1], ?_, ?_⟩
      · unfold cntBody
        refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq hr1 (Run.assign ?_))).mono ?_
        · simp only [evalB_bin_iff, evalB_var_iff]
          exact ⟨_, _, ⟨rfl, by rw [hzk1, hzk]; omega⟩, ⟨rfl, by omega⟩, rfl, by rw [hzk1, hzk]; omega⟩
        · simp only [Expr.size]; omega
      · exact hS.setVar (by decide) _ _ (hS.setVar (by decide) _ _ hD1)
      · simp only [vars_setVar, if_true, show ("zk" : String) ≠ "zbb" by decide, if_false, hzk1, hzk, hzq1,
          length_filter_range_succ, hf, blkW, hAl])
  refine ⟨σ', (Run.seq (Run.assign (evalB_lit (by omega))) hr).mono ?_, hD'.1, hD'.2, ?_⟩
  · simp only [cntCost, Expr.size]; nlinarith
  · rw [hzk', cntW]

end Lax185574Proofs.FarRam
