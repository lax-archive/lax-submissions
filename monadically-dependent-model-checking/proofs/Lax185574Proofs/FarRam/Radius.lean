import Lax185574Proofs.FarRam.Loops


/-!
The radius search of the far-tree program.

`canonFill` stores the canonical blocks `canonW X s ℓ i` of the test
radius `s` in `bt`. `badOuter` tests the admissibility of the blocks in
`bt` at the radii `s₁` and `s₂`. `radSearch` finds the first admissible
radius `radW X r ℓ` and leaves its canonical blocks in `bt`.
-/

namespace Lax185574Proofs.FarRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.EvalRam
open Lax3.DistFO (rhoMinus)

/-! ### The canonical blocks -/

def canonTest : Com :=
  .seq (.assign "hy" (.lit 0)) (.seq (.assign "hs" (.var "s1")) (.seq (.assign "hi" (.var "zi"))
    (.seq (.assign "hj" (.var "zj")) hitC)))

def canonBody : Com :=
  .seq (.assign "zr" (.var "zi")) (.seq (.assign "zj" (.lit 0))
    (.seq (findLoop "zj" "hl" "zr" "v" canonTest) (.store "bt" (.var "zi") (.var "zr"))))

def canonFill : Com := forUp "zi" (.var "hl") canonBody

/-- The facts about the root that the radius search keeps. -/
def RootAt (X : List ℕ) (ℓ : ℕ) (τ : Env) : Prop :=
  τ.arrs "x" = X ∧ (τ.arrs "f").length = 4 ∧ τ.vars "hl" = ℓ

theorem canonTest_spec (B : ℕ) (X : List ℕ) (ℓ s i j : ℕ) (C : Env → Prop) (hC : Stable C canonTest)
    (hL : ListFacts X 0) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) (hs : s < B)
    (hi : i < B) (hj : j < B) :
    Spec B (fun τ => C τ ∧ RootAt X ℓ τ ∧ τ.vars "s1" = s ∧ τ.vars "zi" = i ∧ τ.vars "zj" = j)
      canonTest (fun _ τ' => C τ' ∧ τ'.vars "v" = bv (hit X 0 s i j)) (70 * X.length + 120) := by
  rintro τ ⟨hCτ, ⟨hx, hf, hl⟩, hs1, hzi, hzj⟩
  set τ1 := (((τ.setVar "hy" 0).setVar "hs" s).setVar "hi" i).setVar "hj" j
  have hS : Stable C hitC := hC.mono (by decide) (by decide)
  obtain ⟨τ2, hr2, hC2, hv2⟩ := hitC_spec B X 0 s i j C hS hL hX hXB hs hi hj τ1
    ⟨hC.setVar (by decide) _ _ (hC.setVar (by decide) _ _ (hC.setVar (by decide) _ _
      (hC.setVar (by decide) _ _ hCτ))), by simp [τ1, hx], by simp [τ1, hf], by simp [τ1],
      by simp [τ1], by simp [τ1], by simp [τ1]⟩
  refine ⟨τ2, ?_, hC2, hv2⟩
  unfold canonTest
  refine (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (v := s) ?_)
    (Run.seq (Run.assign (v := i) ?_) (Run.seq (Run.assign (v := j) ?_) hr2)))).mono (by simp; omega)
  · simp only [evalB_var_iff, vars_setVar]; simp [hs1]; omega
  · simp only [evalB_var_iff, vars_setVar]; simp [hzi]; omega
  · simp only [evalB_var_iff, vars_setVar]; simp [hzj]; omega

/-- The blocks in `bt`. -/
def BtAt (X : List ℕ) (ℓ s : ℕ) (k : ℕ) (τ : Env) : Prop :=
  ℓ ≤ (τ.arrs "bt").length ∧ ∀ i < k, (τ.arrs "bt")[i]? = some (canonW X s ℓ i)

theorem canonW_lt (X : List ℕ) (s ℓ i : ℕ) (hi : i < ℓ) : canonW X s ℓ i < ℓ := by
  unfold canonW
  cases h : (List.range ℓ).find? (fun j => hit X 0 s i j) with
  | none => simpa
  | some j => simpa using List.mem_range.mp (List.mem_of_find?_eq_some h)

theorem stable_var {c : Com} (z : String) (n : ℕ) (hz : z ∉ c.wvars) :
    Stable (fun τ => τ.vars z = n) c := fun τ τ' h1 _ _ _ _ h => by
  show τ'.vars z = n; rw [h1 z hz]; exact h

theorem stable_rootAt {c : Com} (X : List ℕ) (ℓ : ℕ) (hx : "x" ∉ c.warrs) (hl : "hl" ∉ c.wvars) :
    Stable (RootAt X ℓ) c := fun τ τ' h1 h2 h3 _ _ h =>
  ⟨by rw [h2 "x" hx]; exact h.1, by rw [h3 "f"]; exact h.2.1, by rw [h1 "hl" hl]; exact h.2.2⟩

theorem stable_btAt {c : Com} (X : List ℕ) (ℓ s k : ℕ) (hb : "bt" ∉ c.warrs) :
    Stable (BtAt X ℓ s k) c := fun τ τ' _ h2 _ _ _ h => by rw [BtAt, h2 "bt" hb]; exact h

def canonCost (X : List ℕ) (ℓ : ℕ) : ℕ := ℓ * (ℓ * (70 * X.length + 140) + 40) + 6

theorem canonFill_spec (B : ℕ) (X : List ℕ) (ℓ s : ℕ) (C : Env → Prop) (hC : Stable C canonFill)
    (hL : ListFacts X 0) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) (hs : s < B)
    (hℓB : ℓ + 1 < B) :
    Spec B (fun τ => C τ ∧ RootAt X ℓ τ ∧ τ.vars "s1" = s ∧ BtAt X ℓ s 0 τ) canonFill
      (fun _ τ' => C τ' ∧ RootAt X ℓ τ' ∧ τ'.vars "s1" = s ∧ BtAt X ℓ s ℓ τ') (canonCost X ℓ) := by
  rintro σ ⟨hCσ, hR, hs1, hbt⟩
  obtain ⟨σ', hr, hI, -⟩ := forUp_run (B := B) (i := "zi") (e := .var "hl") (body := canonBody)
    (N := ℓ) (K := ℓ * (70 * X.length + 140) + 30)
    (fun k τ => C τ ∧ RootAt X ℓ τ ∧ τ.vars "s1" = s ∧ BtAt X ℓ s k τ) (σ := σ) (by omega)
    (fun k _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.1.2.2.symm, by rw [hI.2.1.2.2]; omega⟩)
    ⟨hC.setVar (by decide) _ _ hCσ, by simpa [RootAt] using hR, by simp [hs1], by
      simpa [BtAt] using hbt⟩
    (fun k hk τ hI hik => by
      obtain ⟨hC0, hR0, hs0, hb0⟩ := hI
      let FL := findLoop "zj" "hl" "zr" "v" canonTest
      let C' : Env → Prop := fun ρ => C ρ ∧ RootAt X ℓ ρ ∧ ρ.vars "s1" = s ∧ BtAt X ℓ s k ρ ∧
        ρ.vars "zi" = k
      have hSC : Stable C' FL :=
        (hC.mono (by decide) (by decide)).and ((stable_rootAt X ℓ (by decide) (by decide)).and
          ((stable_var "s1" s (by decide)).and ((stable_btAt X ℓ s k (by decide)).and
            (stable_var "zi" k (by decide)))))
      have hbody : ∀ c, 0 ≤ c → c < ℓ → Spec B (fun ρ => C' ρ ∧ ρ.vars "zj" = c ∧ ρ.vars "hl" = ℓ ∧
          ρ.vars "zr" = k) canonTest (fun _ ρ' => C' ρ' ∧ ρ'.vars "zj" = c ∧ ρ'.vars "hl" = ℓ ∧
          ρ'.vars "zr" = k ∧ ρ'.vars "v" = bv (hit X 0 s k c)) (70 * X.length + 120) := by
        intro c _ hc ρ hρ
        have hS2 : Stable (fun ρ => C' ρ ∧ ρ.vars "zj" = c ∧ ρ.vars "hl" = ℓ ∧ ρ.vars "zr" = k)
            canonTest := (hSC.mono (by decide) (by decide)).and ((stable_var "zj" c (by decide)).and
              ((stable_var "hl" ℓ (by decide)).and (stable_var "zr" k (by decide))))
        obtain ⟨ρ', hr', hC', hv'⟩ := canonTest_spec B X ℓ s k c _ hS2 hL hX hXB hs (by omega)
          (by omega) ρ ⟨hρ, hρ.1.2.1, hρ.1.2.2.1, hρ.1.2.2.2.2, hρ.2.1⟩
        exact ⟨ρ', hr', hC'.1, hC'.2.1, hC'.2.2.1, hC'.2.2.2, hv'⟩
      set τ1 := (τ.setVar "zr" k).setVar "zj" 0
      have hC1 : C' τ1 := by
        refine ⟨hC.setVar (by decide) _ _ (hC.setVar (by decide) _ _ hC0), ?_, ?_, ?_, ?_⟩
        · simpa [τ1, RootAt] using hR0
        · simp [τ1, hs0]
        · simpa [τ1, BtAt] using hb0
        · simp [τ1, hik]
      obtain ⟨τ2, hr2, hC2, hzr2, hhl2⟩ := findLoop_run (B := B) (i := "zj") (hi := "hl") (res := "zr")
        (v := "v") (body := canonTest) C' (fun j => hit X 0 s k j) 0 ℓ k (70 * X.length + 120)
        (by omega) (by omega) (by decide) (by decide) (by decide)
        (fun ρ x h => hSC.setVar (by decide) ρ x h) (fun ρ x h => hSC.setVar (by decide) ρ x h)
        hbody τ1 ⟨hC1, by simp [τ1], by simpa [τ1] using hR0.2.2, by simp [τ1]⟩ (Nat.zero_le _)
      have hcw : ((List.range' 0 (ℓ - 0)).find? fun j => hit X 0 s k j).getD k = canonW X s ℓ k := by
        rw [canonW, Nat.sub_zero, List.range_eq_range']
      rw [hcw] at hzr2
      obtain ⟨hC2a, hR2, hs2, hb2, hzi2⟩ := hC2
      have hbl : k < (τ2.arrs "bt").length := by have := hb2.1; omega
      have hcl := canonW_lt X s ℓ k hk
      have hzrB : τ2.vars "zr" < B := by rw [hzr2]; omega
      have hziB : τ2.vars "zi" < B := by rw [hzi2]; omega
      refine ⟨τ2.setArr "bt" k (canonW X s ℓ k), ?_, ?_, ?_⟩
      · unfold canonBody
        refine (Run.seq (Run.assign (v := k) ?_) (Run.seq (Run.assign (evalB_lit (by omega)))
          (Run.seq hr2 (Run.store (idx := k) ?_ ?_ hbl)))).mono ?_
        · simp only [evalB_var_iff]; exact ⟨hik.symm, by omega⟩
        · simp only [evalB_var_iff]; exact ⟨hzi2.symm, hziB⟩
        · simp only [evalB_var_iff]; exact ⟨hzr2.symm, hzrB⟩
        · simp only [Expr.size, Nat.sub_zero]; nlinarith
      · simp [Env.setArr, hzi2]
      · refine ⟨hC.setVar (by decide) _ _ ?_, ?_, ?_, ?_⟩
        · exact (hC.mono (c := .store "bt" (.var "zi") (.var "zr")) (by decide) (by decide)).run
            (Run.store (idx := k) (v := canonW X s ℓ k)
              (by simp only [evalB_var_iff]; exact ⟨hzi2.symm, hziB⟩)
              (by simp only [evalB_var_iff]; exact ⟨hzr2.symm, hzrB⟩) hbl) (by decide) (by decide) hC2a
        · simpa [RootAt, Env.setArr] using hR2
        · simp [Env.setArr, hs2]
        · refine ⟨by simp [Env.setArr]; exact hb2.1, fun i hi => ?_⟩
          simp only [vars_setVar, Env.setArr, if_true, arrs_setVar]
          rcases Nat.lt_or_ge i k with h | h
          · rw [List.getElem?_set_ne (by omega)]; exact hb2.2 i h
          · obtain rfl : i = k := by omega
            rw [List.getElem?_set_self hbl])
  refine ⟨σ', hr.mono ?_, hI⟩
  simp only [canonCost, Expr.size]
  nlinarith

/-! ### The admissibility test -/

def badTest : Com :=
  .seq (.assign "hy" (.lit 0)) (.seq (.assign "hi" (.var "zi")) (.seq (.assign "hj" (.var "zj"))
    (.ite (.eq (.get "bt" (.var "zi")) (.get "bt" (.var "zj")))
      (.seq (.assign "hs" (.var "s1")) (.seq hitC (.assign "v" (.sub (.lit 1) (.var "v")))))
      (.seq (.assign "hs" (.var "s2")) hitC))))

def badInner : Com := anyLoop "zj" "hl" "zb" "v" badTest

def badOuter : Com := anyLoop "zi" "hl" "zc" "zb" (.seq (.assign "zb" (.lit 0)) badInner)

theorem badTest_spec (B : ℕ) (X : List ℕ) (ℓ s₁ s₂ i j : ℕ) (C : Env → Prop) (hC : Stable C badTest)
    (hL : ListFacts X 0) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) (hs₁ : s₁ < B) (hs₂ : s₂ < B)
    (hℓB : ℓ + 1 < B) (hi : i < ℓ) (hj : j < ℓ) :
    Spec B (fun τ => C τ ∧ RootAt X ℓ τ ∧ τ.vars "s1" = s₁ ∧ τ.vars "s2" = s₂ ∧ BtAt X ℓ s₁ ℓ τ ∧
      τ.vars "zi" = i ∧ τ.vars "zj" = j) badTest
      (fun _ τ' => C τ' ∧ τ'.vars "v" = bv (badW X s₁ s₂ ℓ i j)) (70 * X.length + 130) := by
  rintro τ ⟨hCτ, ⟨hx, hf, hl⟩, h1, h2, hbt, hzi, hzj⟩
  set τ1 := ((τ.setVar "hy" 0).setVar "hi" i).setVar "hj" j
  have hC1 : C τ1 := hC.setVar (by decide) _ _ (hC.setVar (by decide) _ _ (hC.setVar (by decide) _ _ hCτ))
  have hbi := hbt.2 i hi
  have hbj := hbt.2 j hj
  have hci := canonW_lt X s₁ ℓ i hi
  have hcj := canonW_lt X s₁ ℓ j hj
  have hc : (Cond.eq (.get "bt" (.var "zi")) (.get "bt" (.var "zj"))).evalB B τ1 =
      some (canonW X s₁ ℓ i == canonW X s₁ ℓ j) := by
    refine evalB_condEq ?_ ?_
    · simp only [evalB_get_iff, evalB_var_iff]
      exact ⟨i, ⟨by simp [τ1, hzi], by simp [τ1, hzi]; omega⟩, by simpa [τ1] using hbi, by omega⟩
    · simp only [evalB_get_iff, evalB_var_iff]
      exact ⟨j, ⟨by simp [τ1, hzj], by simp [τ1, hzj]; omega⟩, by simpa [τ1] using hbj, by omega⟩
  have rA : Run B (.assign "hy" (.lit 0)) τ (τ.setVar "hy" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have rB : Run B (.assign "hi" (.var "zi")) (τ.setVar "hy" 0) ((τ.setVar "hy" 0).setVar "hi" i) 2 :=
    (Run.assign (by simp only [evalB_var_iff]; simp [hzi]; omega)).mono (by simp)
  have rC : Run B (.assign "hj" (.var "zj")) ((τ.setVar "hy" 0).setVar "hi" i) τ1 2 :=
    (Run.assign (by simp only [evalB_var_iff]; simp [hzj]; omega)).mono (by simp)
  have hpre : ∀ (sv : ℕ), sv < B → RootAt X ℓ ((τ1.setVar "hs" sv)) ∧ (τ1.setVar "hs" sv).vars "hy" = 0 ∧
      (τ1.setVar "hs" sv).vars "hs" = sv ∧ (τ1.setVar "hs" sv).vars "hi" = i ∧
      (τ1.setVar "hs" sv).vars "hj" = j := fun sv _ =>
    ⟨⟨by simp [τ1, hx], by simp [τ1, hf], by simp [τ1, hl]⟩, by simp [τ1], by simp, by simp [τ1],
      by simp [τ1]⟩
  have hSh : Stable C hitC := hC.mono (by decide) (by decide)
  by_cases he : canonW X s₁ ℓ i = canonW X s₁ ℓ j
  · obtain ⟨hR, hy, hs, hi', hj'⟩ := hpre s₁ hs₁
    obtain ⟨τ3, hr3, hC3, hv3⟩ := hitC_spec B X 0 s₁ i j C hSh hL hX hXB hs₁ (by omega) (by omega)
      (τ1.setVar "hs" s₁) ⟨hC.setVar (by decide) _ _ hC1, hR.1, hR.2.1, hy, hs, hi', hj'⟩
    have hvB : τ3.vars "v" ≤ 1 := by rw [hv3]; exact bv_le _
    refine ⟨τ3.setVar "v" (1 - τ3.vars "v"), ?_, hC.setVar (by decide) _ _ hC3, ?_⟩
    · unfold badTest
      refine (Run.seq rA (Run.seq rB (Run.seq rC (Run.ite_true (by rw [hc, he]; simp)
        (Run.seq (Run.assign (v := s₁) (by simp only [evalB_var_iff]; simp [τ1, h1]; omega))
          (Run.seq hr3 (Run.assign (v := 1 - τ3.vars "v") ?_))))))).mono ?_
      · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨1, τ3.vars "v", ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
      · simp only [Cond.size, Expr.size]; omega
    · simp only [vars_setVar, if_true, hv3, badW, he]
      cases hit X 0 s₁ i j <;> simp
  · obtain ⟨hR, hy, hs, hi', hj'⟩ := hpre s₂ hs₂
    obtain ⟨τ3, hr3, hC3, hv3⟩ := hitC_spec B X 0 s₂ i j C hSh hL hX hXB hs₂ (by omega) (by omega)
      (τ1.setVar "hs" s₂) ⟨hC.setVar (by decide) _ _ hC1, hR.1, hR.2.1, hy, hs, hi', hj'⟩
    refine ⟨τ3, ?_, hC3, ?_⟩
    · unfold badTest
      refine (Run.seq rA (Run.seq rB (Run.seq rC (Run.ite_false (by rw [hc]; simpa using he)
        (Run.seq (Run.assign (v := s₂) (by simp only [evalB_var_iff]; simp [τ1, h2]; omega))
          hr3))))).mono ?_
      simp only [Cond.size, Expr.size]; omega
    · have he' : (canonW X s₁ ℓ i != canonW X s₁ ℓ j) = true := by simpa [bne_iff_ne] using he
      have he'' : (canonW X s₁ ℓ i == canonW X s₁ ℓ j) = false := beq_eq_false_iff_ne.mpr he
      rw [hv3, badW, he', he'']; simp

def badCost (X : List ℕ) (ℓ : ℕ) : ℕ := ℓ * (ℓ * (70 * X.length + 150) + 30) + 6

/-- The facts the admissibility test keeps. -/
def BadCtx (X : List ℕ) (ℓ s₁ s₂ : ℕ) (τ : Env) : Prop :=
  RootAt X ℓ τ ∧ τ.vars "s1" = s₁ ∧ τ.vars "s2" = s₂ ∧ BtAt X ℓ s₁ ℓ τ

theorem stable_badCtx {c : Com} (X : List ℕ) (ℓ s₁ s₂ : ℕ) (hx : "x" ∉ c.warrs) (hl : "hl" ∉ c.wvars)
    (h1 : "s1" ∉ c.wvars) (h2 : "s2" ∉ c.wvars) (hb : "bt" ∉ c.warrs) : Stable (BadCtx X ℓ s₁ s₂) c :=
  (stable_rootAt X ℓ hx hl).and ((stable_var "s1" s₁ h1).and ((stable_var "s2" s₂ h2).and
    (stable_btAt X ℓ s₁ ℓ hb)))

theorem badOuter_spec (B : ℕ) (X : List ℕ) (ℓ s₁ s₂ : ℕ) (C : Env → Prop) (hC : Stable C badOuter)
    (hL : ListFacts X 0) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) (hs₁ : s₁ < B) (hs₂ : s₂ < B)
    (hℓB : ℓ + 1 < B) :
    Spec B (fun τ => C τ ∧ BadCtx X ℓ s₁ s₂ τ ∧ τ.vars "zc" = 0) badOuter
      (fun _ τ' => C τ' ∧ BadCtx X ℓ s₁ s₂ τ' ∧ τ'.vars "zc" =
        bv ((List.range ℓ).any fun i => (List.range ℓ).any fun j => badW X s₁ s₂ ℓ i j)) (badCost X ℓ) := by
  rintro σ ⟨hCσ, hB, hzc⟩
  let Co : Env → Prop := fun ρ => C ρ ∧ BadCtx X ℓ s₁ s₂ ρ
  have hSo : Stable Co badOuter := hC.and (stable_badCtx X ℓ s₁ s₂ (by decide) (by decide) (by decide)
    (by decide) (by decide))
  obtain ⟨σ', hr, hCo, hzc', -⟩ := anyLoop_run (B := B) (i := "zi") (n := "hl") (flag := "zc") (v := "zb")
    (body := .seq (.assign "zb" (.lit 0)) badInner) Co
    (fun i => (List.range ℓ).any fun j => badW X s₁ s₂ ℓ i j) ℓ (ℓ * (70 * X.length + 150) + 10)
    hℓB (by decide) (by decide) (by decide) (fun ρ x h => hSo.setVar (by decide) ρ x h)
    (fun ρ x h => hSo.setVar (by decide) ρ x h)
    (fun c hc τ ⟨hCo, hzi, hhl, hzc⟩ => by
      let Ci : Env → Prop := fun ρ => Co ρ ∧ ρ.vars "zi" = c ∧ ρ.vars "zc" = τ.vars "zc"
      have hSi : Stable Ci badInner := (hSo.mono (by decide) (by decide)).and
        ((stable_var "zi" c (by decide)).and (stable_var "zc" _ (by decide)))
      have hCi0 : Ci (τ.setVar "zb" 0) :=
        ⟨hSo.setVar (by decide) _ _ hCo, by simp [hzi], by simp⟩
      obtain ⟨τ2, hr2, hCi2, hzb2, hhl2⟩ := anyLoop_run (B := B) (i := "zj") (n := "hl") (flag := "zb")
        (v := "v") (body := badTest) Ci (fun j => badW X s₁ s₂ ℓ c j) ℓ (70 * X.length + 130) hℓB
        (by decide) (by decide) (by decide) (fun ρ x h => hSi.setVar (by decide) ρ x h)
        (fun ρ x h => hSi.setVar (by decide) ρ x h)
        (fun c' hc' ρ ⟨hCiρ, hzj, hhlρ, hzb⟩ => by
          have hS3 : Stable (fun ρ' => Ci ρ' ∧ ρ'.vars "zj" = c' ∧ ρ'.vars "hl" = ℓ ∧
              ρ'.vars "zb" = ρ.vars "zb") badTest := (hSi.mono (by decide) (by decide)).and
            ((stable_var "zj" c' (by decide)).and ((stable_var "hl" ℓ (by decide)).and
              (stable_var "zb" _ (by decide))))
          obtain ⟨ρ', hr', hC', hv'⟩ := badTest_spec B X ℓ s₁ s₂ c c' _ hS3 hL hX hXB hs₁ hs₂ hℓB hc hc'
            ρ ⟨⟨hCiρ, hzj, hhlρ, rfl⟩, hCiρ.1.2.1, hCiρ.1.2.2.1, hCiρ.1.2.2.2.1, hCiρ.1.2.2.2.2,
              hCiρ.2.1, hzj⟩
          exact ⟨ρ', hr', hC'.1, hC'.2.1, hC'.2.2.1, hC'.2.2.2, hv'⟩)
        (τ.setVar "zb" 0) ⟨hCi0, by simp [hhl], by simp⟩
      refine ⟨τ2, (Run.seq (Run.assign (evalB_lit (by omega))) hr2).mono ?_, hCi2.1, hCi2.2.1, hhl2,
        hCi2.2.2, hzb2⟩
      simp only [Expr.size]
      have : ℓ * (70 * X.length + 130 + 20) = ℓ * (70 * X.length + 150) := by ring
      omega)
    σ ⟨⟨hCσ, hB⟩, hB.1.2.2, hzc⟩
  refine ⟨σ', hr.mono ?_, hCo.1, hCo.2, hzc'⟩
  simp only [badCost]; nlinarith

/-! ### The search -/

def radBody : Com :=
  .seq (.assign "s1" (.sub (.mul (.lit 4) (.var "rr")) (.mul (.lit 2) (.var "r0"))))
    (.seq (.assign "s2" (.add (.mul (.lit 4) (.var "rr")) (.mul (.lit 2) (.var "r0"))))
      (.seq canonFill (.seq (.assign "zc" (.lit 0)) (.seq badOuter
        (.assign "zv" (.sub (.lit 1) (.var "zc")))))))

theorem bv_not (b : Bool) : bv (!b) = 1 - bv b := by cases b <;> rfl

theorem radBody_spec (B : ℕ) (X : List ℕ) (ℓ r ρ : ℕ) (C : Env → Prop) (hC : Stable C radBody)
    (hL : ListFacts X 0) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) (hℓB : ℓ + 1 < B)
    (hρB : 4 * ρ + 2 * r < B) :
    Spec B (fun τ => C τ ∧ RootAt X ℓ τ ∧ τ.vars "r0" = r ∧ τ.vars "rr" = ρ ∧ ℓ ≤ (τ.arrs "bt").length)
      radBody (fun _ τ' => C τ' ∧ RootAt X ℓ τ' ∧ τ'.vars "r0" = r ∧ τ'.vars "rr" = ρ ∧
        ℓ ≤ (τ'.arrs "bt").length ∧ τ'.vars "zv" = bv (admW X r ρ ℓ))
      (canonCost X ℓ + badCost X ℓ + 40) := by
  rintro τ ⟨hCτ, hR, hr0, hrr, hbl⟩
  let D : Env → Prop := fun ρ' => C ρ' ∧ ρ'.vars "r0" = r ∧ ρ'.vars "rr" = ρ
  have hSD : Stable D radBody := hC.and ((stable_var "r0" r (by decide)).and (stable_var "rr" ρ (by decide)))
  set s₁ := 4 * ρ - 2 * r
  set s₂ := 4 * ρ + 2 * r
  set τ1 := (τ.setVar "s1" s₁).setVar "s2" s₂
  have rA : Run B (.assign "s1" (.sub (.mul (.lit 4) (.var "rr")) (.mul (.lit 2) (.var "r0")))) τ
      (τ.setVar "s1" s₁) 10 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨4 * ρ, 2 * r, ⟨4, ρ, ⟨rfl, by omega⟩, ⟨hrr.symm, by omega⟩, rfl, by omega⟩,
      ⟨2, r, ⟨rfl, by omega⟩, ⟨hr0.symm, by omega⟩, rfl, by omega⟩, rfl, by omega⟩
  have rB : Run B (.assign "s2" (.add (.mul (.lit 4) (.var "rr")) (.mul (.lit 2) (.var "r0"))))
      (τ.setVar "s1" s₁) τ1 10 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, vars_setVar]
    exact ⟨4 * ρ, 2 * r, ⟨4, ρ, ⟨rfl, by omega⟩, ⟨by simp [hrr], by simp [hrr]; omega⟩, rfl, by omega⟩,
      ⟨2, r, ⟨rfl, by omega⟩, ⟨by simp [hr0], by simp [hr0]; omega⟩, rfl, by omega⟩, rfl, by omega⟩
  have hD1 : D τ1 := ⟨hC.setVar (by decide) _ _ (hC.setVar (by decide) _ _ hCτ), by simp [τ1, hr0],
    by simp [τ1, hrr]⟩
  have hSc : Stable (fun ρ' => D ρ' ∧ ρ'.vars "s2" = s₂) canonFill :=
    (hSD.mono (by decide) (by decide)).and (stable_var "s2" s₂ (by decide))
  obtain ⟨τ2, hr2, ⟨hD2, hs22⟩, hR2, hs12, hbt2⟩ := canonFill_spec B X ℓ s₁ _ hSc hL hX hXB (by omega)
    hℓB τ1 ⟨⟨hD1, by simp [τ1]⟩, by simpa [τ1, RootAt] using hR, by simp [τ1], by
      refine ⟨by simpa [τ1] using hbl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
  set τ3 := τ2.setVar "zc" 0
  have hSb : Stable D badOuter := hSD.mono (by decide) (by decide)
  obtain ⟨τ4, hr4, hD4, hB4, hzc4⟩ := badOuter_spec B X ℓ s₁ s₂ D hSb hL hX hXB (by omega) (by omega)
    hℓB τ3 ⟨hSD.setVar (by decide) _ _ hD2, ⟨by simpa [τ3, RootAt] using hR2, by simp [τ3, hs12],
      by simp [τ3, hs22], by simpa [τ3, BtAt] using hbt2⟩, by simp [τ3]⟩
  have hzcl : τ4.vars "zc" ≤ 1 := by rw [hzc4]; exact bv_le _
  refine ⟨τ4.setVar "zv" (1 - τ4.vars "zc"), ?_, hSD.setVar (by decide) _ _ hD4 |>.1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold radBody
    refine (Run.seq rA (Run.seq rB (Run.seq hr2 (Run.seq
      (Run.assign (evalB_lit (by omega))) (Run.seq hr4 (Run.assign (v := 1 - τ4.vars "zc") ?_)))))).mono ?_
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨1, τ4.vars "zc", ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
    · simp only [Expr.size]; omega
  · simpa [RootAt] using hB4.1
  · simpa using hD4.2.1
  · simpa using hD4.2.2
  · simpa using hB4.2.2.2.1
  · show (τ4.setVar "zv" (1 - τ4.vars "zc")).vars "zv" = _
    simp [hzc4, admW, bv_not, s₁, s₂]

theorem stable_len {c : Com} (a : String) (n : ℕ) : Stable (fun τ => n ≤ (τ.arrs a).length) c :=
  fun τ τ' _ _ h3 _ _ h => by show n ≤ (τ'.arrs a).length; rw [h3 a]; exact h

theorem radW_bounds (X : List ℕ) (r ℓ : ℕ) :
    r ≤ radW X r ℓ ∧ radW X r ℓ ≤ max r (9 ^ (ℓ - 1) * r) := by
  unfold radW
  cases h : (List.range' r (9 ^ (ℓ - 1) * r - r + 1)).find? (fun ρ => admW X r ρ ℓ) with
  | none => simp
  | some ρ =>
    have := List.mem_range'.mp (List.mem_of_find?_eq_some h)
    simp only [Option.getD_some]
    omega

def radPhase : Com :=
  .seq (.assign "ze" (.mul (.add (.add (.var "hk") (.var "hq")) (.lit 1)) (.sub (.var "hq") (.lit 1))))
  (.seq (powLoop "r0" "zi" "ze")
  (.seq (.assign "ze" (.sub (.var "hl") (.lit 1)))
  (.seq (powLoop "ru" "zi" "ze")
  (.seq (.assign "ru" (.mul (.var "ru") (.var "r0")))
  (.seq (.assign "rh" (.add (.var "ru") (.lit 1)))
  (.seq (.assign "rr" (.var "r0"))
  (.seq (.assign "rho" (.var "r0"))
  (.seq (findLoop "rr" "rh" "rho" "zv" radBody)
  (.seq (.assign "s1" (.sub (.mul (.lit 4) (.var "rho")) (.mul (.lit 2) (.var "r0"))))
   canonFill)))))))))

def radCost (X : List ℕ) (ℓ E U : ℕ) : ℕ :=
  20 * E + 20 * ℓ + 100 + (canonCost X ℓ + badCost X ℓ + 60) * (U + 1) + canonCost X ℓ

theorem rhoMinus_succ (k q : ℕ) : rhoMinus (k + 1) q = 9 ^ ((k + (q + 1) + 1) * q) := by
  rw [Lax3.DistFO.rhoMinus]; ring_nf

/-- **The radius search.** -/
theorem radPhase_spec (B : ℕ) (X : List ℕ) (k q ℓ : ℕ) (C : Env → Prop) (hC : Stable C radPhase)
    (hL : ListFacts X 0) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) (hℓB : ℓ + 1 < B)
    (hRB : 4 * (9 ^ (ℓ - 1) * rhoMinus (k + 1) q) + 2 * rhoMinus (k + 1) q + 2 < B)
    (hEB : (k + (q + 1) + 1) * q + 1 < B) (hkB : k + q + 3 < B) (h9 : 9 < B) :
    Spec B (fun τ => C τ ∧ RootAt X ℓ τ ∧ τ.vars "hk" = k ∧ τ.vars "hq" = q + 1 ∧
        ℓ ≤ (τ.arrs "bt").length) radPhase
      (fun _ τ' => C τ' ∧ RootAt X ℓ τ' ∧ τ'.vars "hk" = k ∧ τ'.vars "hq" = q + 1 ∧
        τ'.vars "r0" = rhoMinus (k + 1) q ∧ τ'.vars "rho" = radW X (rhoMinus (k + 1) q) ℓ ∧
        BtAt X ℓ (4 * radW X (rhoMinus (k + 1) q) ℓ - 2 * rhoMinus (k + 1) q) ℓ τ')
      (radCost X ℓ ((k + (q + 1) + 1) * q) (9 ^ (ℓ - 1) * rhoMinus (k + 1) q)) := by
  rintro τ ⟨hCτ, hR, hk, hq, hbl⟩
  set r := rhoMinus (k + 1) q with hr
  set E := (k + (q + 1) + 1) * q with hE
  set U := 9 ^ (ℓ - 1) * r with hU
  have hr9 : r = 9 ^ E := by rw [hr, rhoMinus_succ]
  have hr1 : 1 ≤ r := by rw [hr9]; exact Nat.one_le_pow _ _ (by norm_num)
  have hrU : r ≤ U := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))
  have h9U : 9 ^ (ℓ - 1) ≤ U := Nat.le_mul_of_pos_right _ hr1
  have hrB : r < B := by omega
  let D : Env → Prop := fun ρ => C ρ ∧ RootAt X ℓ ρ ∧ ρ.vars "hk" = k ∧ ρ.vars "hq" = q + 1 ∧
    ℓ ≤ (ρ.arrs "bt").length
  have hSD : Stable D radPhase := hC.and ((stable_rootAt X ℓ (by decide) (by decide)).and
    ((stable_var "hk" k (by decide)).and ((stable_var "hq" (q + 1) (by decide)).and (stable_len "bt" ℓ))))
  have hD0 : D τ := ⟨hCτ, hR, hk, hq, hbl⟩
  -- the exponent and the radius
  have rE : Run B (.assign "ze" (.mul (.add (.add (.var "hk") (.var "hq")) (.lit 1))
      (.sub (.var "hq") (.lit 1)))) τ (τ.setVar "ze" E) 12 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    refine ⟨k + (q + 1) + 1, q, ⟨k + (q + 1), 1, ⟨k, q + 1, ⟨hk.symm, by omega⟩, ⟨hq.symm, by omega⟩,
      rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩, ⟨q + 1, 1, ⟨hq.symm, by omega⟩, ⟨rfl, by omega⟩,
      by simp [Bop.apply], by omega⟩, rfl, by omega⟩
  obtain ⟨τ1, r1, hD1, hr01, -⟩ := powLoop_run (B := B) (x := "r0") (i := "zi") (n := "ze") D E
    (by rw [← hr9]; exact hrB) h9 (by omega) (by decide) (by decide) (by decide)
    (fun ρ v h => hSD.setVar (by decide) ρ v h) (fun ρ v h => hSD.setVar (by decide) ρ v h)
    (τ.setVar "ze" E) ⟨hSD.setVar (by decide) _ _ hD0, by simp⟩
  rw [← hr9] at hr01
  let D2 : Env → Prop := fun ρ => D ρ ∧ ρ.vars "r0" = r
  have hD2s : ∀ z, z ∈ radPhase.wvars → z ≠ "r0" → ∀ ρ v, D2 ρ → D2 (ρ.setVar z v) :=
    fun z hz hz' ρ v h => ⟨hSD.setVar hz ρ v h.1, by simp [vars_setVar, Ne.symm hz', h.2]⟩
  have hl1 : τ1.vars "hl" = ℓ := hD1.2.1.2.2
  have rE2 : Run B (.assign "ze" (.sub (.var "hl") (.lit 1))) τ1 (τ1.setVar "ze" (ℓ - 1)) 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨ℓ, 1, ⟨hl1.symm, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
  obtain ⟨τ2, r2, hD2, hru2, -⟩ := powLoop_run (B := B) (x := "ru") (i := "zi") (n := "ze") D2 (ℓ - 1)
    (by omega) h9 (by omega) (by decide) (by decide) (by decide)
    (hD2s "ru" (by decide) (by decide)) (hD2s "zi" (by decide) (by decide))
    (τ1.setVar "ze" (ℓ - 1)) ⟨hD2s "ze" (by decide) (by decide) _ _ ⟨hD1, hr01⟩, by simp⟩
  set τ3 := ((((τ2.setVar "ru" U).setVar "rh" (U + 1)).setVar "rr" r).setVar "rho" r) with hτ3
  have rU : Run B (.assign "ru" (.mul (.var "ru") (.var "r0"))) τ2 (τ2.setVar "ru" U) 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff]
    exact ⟨9 ^ (ℓ - 1), r, ⟨hru2.symm, by omega⟩, ⟨hD2.2.symm, by omega⟩, by simp [Bop.apply, hU], by omega⟩
  have rH : Run B (.assign "rh" (.add (.var "ru") (.lit 1))) (τ2.setVar "ru" U)
      ((τ2.setVar "ru" U).setVar "rh" (U + 1)) 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨U, 1, ⟨by simp, by simp; omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
  have rR : Run B (.assign "rr" (.var "r0")) ((τ2.setVar "ru" U).setVar "rh" (U + 1))
      (((τ2.setVar "ru" U).setVar "rh" (U + 1)).setVar "rr" r) 2 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_var_iff]; simp [hD2.2]; omega
  have rO : Run B (.assign "rho" (.var "r0")) (((τ2.setVar "ru" U).setVar "rh" (U + 1)).setVar "rr" r)
      τ3 2 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_var_iff]; simp [hD2.2]; omega
  have hD3 : D2 τ3 := by
    rw [hτ3]
    exact hD2s "rho" (by decide) (by decide) _ _ (hD2s "rr" (by decide) (by decide) _ _
      (hD2s "rh" (by decide) (by decide) _ _ (hD2s "ru" (by decide) (by decide) _ _ hD2)))
  obtain ⟨τ4, r4, hD4, hrho4, hrh4⟩ := findLoop_run (B := B) (i := "rr") (hi := "rh") (res := "rho")
    (v := "zv") (body := radBody) D2 (fun ρ => admW X r ρ ℓ) r (U + 1) r
    (canonCost X ℓ + badCost X ℓ + 40) (by omega) (by omega) (by decide) (by decide) (by decide)
    (hD2s "rr" (by decide) (by decide)) (hD2s "rho" (by decide) (by decide))
    (fun c hc1 hc2 ρ ⟨hDρ, hrr, hrh, hrho⟩ => by
      have hS : Stable (fun ρ' => C ρ' ∧ ρ'.vars "hk" = k ∧ ρ'.vars "hq" = q + 1 ∧
          ρ'.vars "rh" = U + 1 ∧ ρ'.vars "rho" = r) radBody :=
        (hC.mono (by decide) (by decide)).and ((stable_var "hk" k (by decide)).and
          ((stable_var "hq" (q + 1) (by decide)).and ((stable_var "rh" (U + 1) (by decide)).and
            (stable_var "rho" r (by decide)))))
      obtain ⟨ρ', hr', ⟨hC', hk', hq', hrh', hrho'⟩, hR', hr0', hrr', hbl', hzv'⟩ :=
        radBody_spec B X ℓ r c _ hS hL hX hXB hℓB (by omega) ρ
          ⟨⟨hDρ.1.1, hDρ.1.2.2.1, hDρ.1.2.2.2.1, hrh, hrho⟩, hDρ.1.2.1, hDρ.2, hrr, hDρ.1.2.2.2.2⟩
      exact ⟨ρ', hr', ⟨⟨hC', hR', hk', hq', hbl'⟩, hr0'⟩, hrr', hrh', hrho', hzv'⟩)
    τ3 ⟨hD3, by simp [hτ3], by simp [hτ3], by simp [hτ3]⟩ (by omega)
  have hρw : ((List.range' r (U + 1 - r)).find? fun ρ => admW X r ρ ℓ).getD r = radW X r ℓ := by
    rw [radW, ← hU, show U + 1 - r = U - r + 1 by omega]
  rw [hρw] at hrho4
  set ρs := radW X r ℓ with hρs
  obtain ⟨hρ1, hρ2⟩ := radW_bounds X r ℓ
  have hρU : ρs ≤ U := le_trans hρ2 (max_le hrU le_rfl)
  set τ5 := τ4.setVar "s1" (4 * ρs - 2 * r)
  have r5 : Run B (.assign "s1" (.sub (.mul (.lit 4) (.var "rho")) (.mul (.lit 2) (.var "r0")))) τ4 τ5 10 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨4 * ρs, 2 * r, ⟨4, ρs, ⟨rfl, by omega⟩, ⟨hrho4.symm, by omega⟩, rfl, by omega⟩,
      ⟨2, r, ⟨rfl, by omega⟩, ⟨hD4.2.symm, by omega⟩, rfl, by omega⟩, rfl, by omega⟩
  have hS6 : Stable (fun ρ' => C ρ' ∧ ρ'.vars "hk" = k ∧ ρ'.vars "hq" = q + 1 ∧
      ρ'.vars "r0" = r ∧ ρ'.vars "rho" = ρs) canonFill :=
    (hC.mono (by decide) (by decide)).and ((stable_var "hk" k (by decide)).and
      ((stable_var "hq" (q + 1) (by decide)).and ((stable_var "r0" r (by decide)).and
        (stable_var "rho" ρs (by decide)))))
  obtain ⟨τ6, r6, ⟨hC6, hk6, hq6, hr06, hrho6⟩, hR6, -, hbt6⟩ := canonFill_spec B X ℓ (4 * ρs - 2 * r) _
    hS6 hL hX hXB (by omega) hℓB τ5
    ⟨⟨hC.setVar (by decide) _ _ hD4.1.1, by simp [τ5, hD4.1.2.2.1], by simp [τ5, hD4.1.2.2.2.1],
      by simp [τ5, hD4.2], by simp [τ5, hrho4]⟩, by simpa [τ5, RootAt] using hD4.1.2.1, by simp [τ5],
      ⟨by simpa [τ5] using hD4.1.2.2.2.2, fun i hi => absurd hi (Nat.not_lt_zero _)⟩⟩
  refine ⟨τ6, ?_, hC6, hR6, hk6, hq6, hr06, hrho6, hbt6⟩
  unfold radPhase
  refine (Run.seq rE (Run.seq r1 (Run.seq rE2 (Run.seq r2 (Run.seq rU (Run.seq rH (Run.seq rR
    (Run.seq rO (Run.seq r4 (Run.seq r5 r6)))))))))).mono ?_
  simp only [radCost]
  have : (canonCost X ℓ + badCost X ℓ + 40 + 20) * (U + 1 - r) ≤
      (canonCost X ℓ + badCost X ℓ + 60) * (U + 1) := Nat.mul_le_mul (by omega) (by omega)
  have : (ℓ - 1) * 20 ≤ 20 * ℓ := by omega
  omega

end Lax185574Proofs.FarRam

