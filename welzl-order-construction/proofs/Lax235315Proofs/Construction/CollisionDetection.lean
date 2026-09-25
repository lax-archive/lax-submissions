import Lax235315Proofs.Construction.RadixEight
import Mathlib.Tactic

/-! Correctness of the adjacent-key collision detector. -/

namespace Lax235315Proofs.Construction.CollisionDetection

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.RandomKeysRead
open Lax235315Proofs.Construction.RadixMath
open Lax235315Proofs.Construction.WelzlProgram

def EqualOn (value : String → ℕ → ℕ) (keys : List String)
    (left right : ℕ) : Prop :=
  ∀ key ∈ keys, value key left = value key right

instance equalOnDecidable (value : String → ℕ → ℕ) (keys : List String)
    (left right : ℕ) : Decidable (EqualOn value keys left right) := by
  unfold EqualOn
  infer_instance

@[simp] theorem checkAllDigitsEqual_warrs (keys : List String) :
    (checkAllDigitsEqual keys).warrs = [] := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp [checkAllDigitsEqual, Com.warrs, ih]

@[simp] theorem checkAllDigitsEqual_wvars (keys : List String) :
    (checkAllDigitsEqual keys).wvars = ["collision"] := by
  induction keys with
  | nil => rfl
  | cons key keys ih => simp [checkAllDigitsEqual, Com.wvars, ih]

/-- The short-circuit comparison sets `collision` precisely when every
listed array agrees at `left` and `right`. -/
theorem checkAllDigitsEqual_run {B n left right : ℕ}
    {value : String → ℕ → ℕ} {keys : List String} {σ : Env}
    (hleft : σ.vars "left" = left) (hright : σ.vars "right" = right)
    (hleftn : left < n) (hrightn : right < n)
    (harrays : ∀ key ∈ keys, σ.arrs key = arrOf n (value key))
    (hvalueB : ∀ key ∈ keys, ∀ i < n, value key i < B)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ', Run B (checkAllDigitsEqual keys) σ σ'
        (20 * (keys.length + 1)) ∧
      σ'.vars "collision" =
        if EqualOn value keys left right then 1 else σ.vars "collision" := by
  classical
  induction keys with
  | nil =>
      let σ' := σ.setVar "collision" 1
      refine ⟨σ', (Run.assign (evalB_lit honeB)).mono (by
        norm_num [Expr.size]), ?_⟩
      simp [σ', EqualOn]
  | cons key keys ih =>
      have hkeyArr : σ.arrs key = arrOf n (value key) := harrays key (by simp)
      have hleftGet : (σ.arrs key)[left]? = some (value key left) := by
        rw [hkeyArr, getElem?_arrOf _ hleftn]
      have hrightGet : (σ.arrs key)[right]? = some (value key right) := by
        rw [hkeyArr, getElem?_arrOf _ hrightn]
      have hleftEval : (Expr.get key (.var "left")).evalB B σ =
          some (value key left) := by
        apply evalB_get
        · rw [evalB_var_iff]
          exact ⟨hleft.symm, by rw [hleft]; exact hleftn.trans hnB⟩
        · exact hleftGet
        · exact hvalueB key (by simp) left hleftn
      have hrightEval : (Expr.get key (.var "right")).evalB B σ =
          some (value key right) := by
        apply evalB_get
        · rw [evalB_var_iff]
          exact ⟨hright.symm, by rw [hright]; exact hrightn.trans hnB⟩
        · exact hrightGet
        · exact hvalueB key (by simp) right hrightn
      let test := Cond.eq (.get key (.var "left")) (.get key (.var "right"))
      by_cases heq : value key left = value key right
      · have htest : test.evalB B σ = some true := by
          simpa [test, heq] using evalB_condEq hleftEval hrightEval
        obtain ⟨σ', r, hcollision⟩ := ih
          (fun a ha => harrays a (by simp [ha]))
          (fun a ha => hvalueB a (by simp [ha]))
        refine ⟨σ', (Run.ite_true htest r).mono (by
          simp [test, Cond.size, Expr.size]
          omega), ?_⟩
        simpa [EqualOn, heq] using hcollision
      · have htest : test.evalB B σ = some false := by
          simpa [test, heq] using evalB_condEq hleftEval hrightEval
        refine ⟨σ, (Run.ite_false htest Run.skip).mono (by
          simp [test, Cond.size, Expr.size]
          omega), ?_⟩
        simp [EqualOn, heq]

def AdjacentBefore (value : String → ℕ → ℕ) (keys : List String)
    (xs : List ℕ) (i : ℕ) : Prop :=
  ∃ j, 1 ≤ j ∧ j < i ∧
    EqualOn value keys (xs.getD (j - 1) 0) (xs.getD j 0)

noncomputable instance adjacentBeforeDecidable (value : String → ℕ → ℕ)
    (keys : List String) (xs : List ℕ) (i : ℕ) :
    Decidable (AdjacentBefore value keys xs i) := Classical.propDecidable _

theorem adjacentBefore_succ {value : String → ℕ → ℕ} {keys : List String}
    {xs : List ℕ} {i : ℕ} (hi : 1 ≤ i) :
    AdjacentBefore value keys xs (i + 1) ↔
      AdjacentBefore value keys xs i ∨
        EqualOn value keys (xs.getD (i - 1) 0) (xs.getD i 0) := by
  constructor
  · rintro ⟨j, hj1, hji, heq⟩
    by_cases hj : j < i
    · exact Or.inl ⟨j, hj1, hj, heq⟩
    · right
      have : j = i := by omega
      simpa [this] using heq
  · rintro (⟨j, hj1, hji, heq⟩ | heq)
    · exact ⟨j, hj1, by omega, heq⟩
    · exact ⟨i, hi, by omega, heq⟩

def DetectInv (n : ℕ) (value : String → ℕ → ℕ) (xs : List ℕ)
    (ord : ℕ → ℕ) (τ : Env) : Prop :=
  τ.vars "alen" = xs.length ∧
    1 ≤ τ.vars "i" ∧ τ.vars "i" ≤ max 1 xs.length ∧
    τ.arrs "ord" = arrOf n ord ∧
    (∀ j < xs.length, ord j = xs.getD j 0) ∧
    (∀ key ∈ keyNames, τ.arrs key = arrOf n (value key)) ∧
    τ.vars "collision" =
      if AdjacentBefore value keyNames xs (τ.vars "i") then 1 else 0

/-- `detectCollision` checks exactly all adjacent pairs in `ord`. -/
theorem detectCollision_run {B n : ℕ} {value : String → ℕ → ℕ}
    {xs : List ℕ} {ord : ℕ → ℕ} {σ : Env}
    (halen : σ.vars "alen" = xs.length)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hordval : ∀ j < xs.length, ord j = xs.getD j 0)
    (harrays : ∀ key ∈ keyNames, σ.arrs key = arrOf n (value key))
    (hvalueB : ∀ key ∈ keyNames, ∀ i < n, value key i < B)
    (hvert : ∀ x ∈ xs, x < n) (hxn : xs.length ≤ n)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ', Run B detectCollision σ σ' (300 * (xs.length + 1)) ∧
      σ'.vars "collision" =
        if AdjacentBefore value keyNames xs xs.length then 1 else 0 := by
  classical
  let σ₀ := σ.setVar "collision" 0
  have r₀ : Run B (.assign "collision" (.lit 0)) σ σ₀ 2 := by
    simpa [σ₀, Expr.size] using Run.assign (evalB_lit (by omega : 0 < B))
  let σ₁ := σ₀.setVar "i" 1
  have r₁ : Run B (.assign "i" (.lit 1)) σ₀ σ₁ 2 := by
    simpa [σ₁, Expr.size] using Run.assign (evalB_lit honeB)
  have hinit : DetectInv n value xs ord σ₁ := by
    refine ⟨by simp [σ₁, σ₀, halen], by simp [σ₁], by simp [σ₁],
      by simp [σ₁, σ₀, hord], hordval, ?_, ?_⟩
    · intro key hkey
      simp [σ₁, σ₀, harrays key hkey]
    · simp [σ₁, σ₀, AdjacentBefore]
  let test := Cond.lt (.var "i") (.var "alen")
  let body := seqs [
    .assign "left" (.get "ord" (.sub (.var "i") (.lit 1))),
    .assign "right" (.get "ord" (.var "i")),
    checkAllDigitsEqual keyNames,
    inc "i"]
  have hdef : ∀ τ, DetectInv n value xs ord τ →
      ∃ v, test.evalB B τ = some v := by
    intro τ hI
    rcases hI with ⟨halenτ, hi1, hiMax, -, -, -, -⟩
    have halenB : τ.vars "alen" < B := by rw [halenτ]; omega
    have hiB : τ.vars "i" < B := by
      by_cases hx : xs.length = 0
      · simp [hx] at hiMax
        omega
      · have : 1 ≤ xs.length := Nat.one_le_iff_ne_zero.mpr hx
        rw [max_eq_right this] at hiMax
        omega
    exact ⟨decide (τ.vars "i" < τ.vars "alen"), by
      simp [test, evalB_condLt_iff, hiB, halenB]⟩
  have hstep : ∀ τ, DetectInv n value xs ord τ →
      test.evalB B τ = some true →
      ∃ τ', Run B body τ τ' 250 ∧
        DetectInv n value xs ord τ' ∧
        xs.length - τ'.vars "i" < xs.length - τ.vars "i" := by
    intro τ hI htest
    rcases hI with ⟨halenτ, hi1, hiMax, hordτ, hordvalτ, harrτ, hcollisionτ⟩
    have hi : τ.vars "i" < xs.length := by
      have ht := htest
      simp [test, evalB_condLt_iff, halenτ] at ht
      exact ht.2.2
    have hiB : τ.vars "i" < B := hi.trans_le hxn |>.trans hnB
    have him1 : τ.vars "i" - 1 < xs.length := by omega
    have hin : τ.vars "i" < n := hi.trans_le hxn
    have him1n : τ.vars "i" - 1 < n := him1.trans_le hxn
    let left := xs.getD (τ.vars "i" - 1) 0
    let right := xs.getD (τ.vars "i") 0
    have hleftMem : left ∈ xs := by
      simp only [left]
      rw [List.getD_eq_getElem _ _ him1]
      exact List.getElem_mem (l := xs) him1
    have hrightMem : right ∈ xs := by
      simp only [right]
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem (l := xs) hi
    have hleftn : left < n := hvert left hleftMem
    have hrightn : right < n := hvert right hrightMem
    have hleftGet : (τ.arrs "ord")[τ.vars "i" - 1]? = some left := by
      rw [hordτ, getElem?_arrOf ord him1n, hordvalτ _ him1]
    have hrightGet : (τ.arrs "ord")[τ.vars "i"]? = some right := by
      rw [hordτ, getElem?_arrOf ord hin, hordvalτ _ hi]
    have hsubEval : (Expr.sub (.var "i") (.lit 1)).evalB B τ =
        some (τ.vars "i" - 1) := by
      apply evalB_bin
      · exact evalB_var hiB
      · exact evalB_lit honeB
      · simp
        omega
    have hleftEval : (Expr.get "ord" (Expr.sub (.var "i") (.lit 1))).evalB B τ =
        some left := evalB_get hsubEval hleftGet (hleftn.trans hnB)
    let τ₁ := τ.setVar "left" left
    have rleft : Run B
        (.assign "left" (.get "ord" (.sub (.var "i") (.lit 1)))) τ τ₁ 8 := by
      exact (Run.assign hleftEval).mono (by norm_num [Expr.size])
    have hiτ₁ : τ₁.vars "i" = τ.vars "i" := by simp [τ₁]
    have hrightGet₁ : (τ₁.arrs "ord")[τ₁.vars "i"]? = some right := by
      simpa [τ₁] using hrightGet
    have hrightEval : (Expr.get "ord" (.var "i")).evalB B τ₁ = some right := by
      apply evalB_get
      · exact evalB_var (by simpa [hiτ₁] using hiB)
      · exact hrightGet₁
      · exact hrightn.trans hnB
    let τ₂ := τ₁.setVar "right" right
    have rright : Run B (.assign "right" (.get "ord" (.var "i"))) τ₁ τ₂ 6 := by
      exact (Run.assign hrightEval).mono (by norm_num [Expr.size])
    obtain ⟨τ₃, rcheck, hcollision₃⟩ :=
      checkAllDigitsEqual_run (σ := τ₂) (value := value)
        (by simp [τ₂, τ₁]) (by simp [τ₂]) hleftn hrightn
        (fun key hkey => by simpa [τ₂, τ₁] using harrτ key hkey)
        hvalueB hnB honeB
    have hiτ₃ : τ₃.vars "i" = τ.vars "i" := by
      rw [rcheck.frame_var "i" (by simp)]
      simp [τ₂, τ₁]
    let τ₄ := τ₃.setVar "i" (τ.vars "i" + 1)
    have rinc : Run B (inc "i") τ₃ τ₄ 4 := by
      apply Run.assign
      apply evalB_bin
      · rw [evalB_var_iff]
        exact ⟨hiτ₃.symm, by rw [hiτ₃]; exact hiB⟩
      · exact evalB_lit honeB
      · simp
        omega
    have rr := rleft.seq (rright.seq (rcheck.seq rinc))
    refine ⟨τ₄, ?_, ?_, ?_⟩
    · simpa [body, seqs] using rr.mono (by norm_num [keyNames])
    · refine ⟨by
          rw [rr.frame_var "alen" (by simp [Com.wvars, inc]), halenτ],
        by simp [τ₄], ?_, ?_, hordvalτ, ?_, ?_⟩
      · change τ.vars "i" + 1 ≤ max 1 xs.length
        exact (Nat.succ_le_of_lt hi).trans (Nat.le_max_right _ _)
      · rw [rr.frame_arr "ord" (by simp [Com.warrs, inc]), hordτ]
      · intro key hkey
        rw [rr.frame_arr key (by simp [Com.warrs, inc]), harrτ key hkey]
      · let current := EqualOn value keyNames left right
        have hcollision₄ : τ₄.vars "collision" =
            if current then 1
            else τ.vars "collision" := by
          simpa [current, τ₄, τ₂, τ₁] using hcollision₃
        have hi₄ : τ₄.vars "i" = τ.vars "i" + 1 := by simp [τ₄]
        have hsucc := adjacentBefore_succ (value := value) (keys := keyNames)
          (xs := xs) hi1
        by_cases hprev : AdjacentBefore value keyNames xs (τ.vars "i")
        · have hadj₄ : AdjacentBefore value keyNames xs (τ₄.vars "i") := by
            rw [hi₄]
            exact hsucc.mpr (Or.inl hprev)
          rw [if_pos hadj₄]
          by_cases hcurrent : current
          · rw [if_pos hcurrent] at hcollision₄
            exact hcollision₄
          · rw [if_neg hcurrent] at hcollision₄
            rw [if_pos hprev] at hcollisionτ
            omega
        · by_cases hcurrent : current
          · have hnow : EqualOn value keyNames
                (xs.getD (τ.vars "i" - 1) 0) (xs.getD (τ.vars "i") 0) := by
              simpa [current, left, right] using hcurrent
            have hadj₄ : AdjacentBefore value keyNames xs (τ₄.vars "i") := by
              rw [hi₄]
              exact hsucc.mpr (Or.inr hnow)
            rw [if_pos hadj₄, if_pos hcurrent] at *
            exact hcollision₄
          · have hnow : ¬EqualOn value keyNames
                (xs.getD (τ.vars "i" - 1) 0) (xs.getD (τ.vars "i") 0) := by
              simpa [current, left, right] using hcurrent
            have hadjSucc : ¬AdjacentBefore value keyNames xs
                (τ.vars "i" + 1) := by
              intro hadj
              rcases hsucc.mp hadj with hold | hnew
              · exact hprev hold
              · exact hnow hnew
            have hadj₄ : ¬AdjacentBefore value keyNames xs (τ₄.vars "i") := by
              simpa [hi₄] using hadjSucc
            rw [if_neg hadj₄]
            rw [if_neg hcurrent] at hcollision₄
            rw [if_neg hprev] at hcollisionτ
            exact hcollision₄.trans hcollisionτ
    · simp [τ₄]
      omega
  obtain ⟨τ₂, rloop, hfinal, hfalse⟩ :=
    Run.while_count (DetectInv n value xs ord)
      (fun τ => xs.length - τ.vars "i") 250 hdef hstep hinit
  rcases hfinal with ⟨halen₂, hi1₂, hiMax₂, -, -, -, hcollision₂⟩
  have hnotlt : ¬τ₂.vars "i" < xs.length := by
    have hf := hfalse
    simp [test, evalB_condLt_iff, halen₂] at hf
    exact Nat.not_lt_of_ge hf.2.2
  have hanswer : τ₂.vars "collision" =
      if AdjacentBefore value keyNames xs xs.length then 1 else 0 := by
    by_cases hx : xs.length = 0
    · have hieq : τ₂.vars "i" = 1 := by
        simp [hx] at hiMax₂
        omega
      simp [hx, hieq, AdjacentBefore] at hcollision₂ ⊢
      exact hcollision₂
    · have hlen1 : 1 ≤ xs.length := Nat.one_le_iff_ne_zero.mpr hx
      rw [max_eq_right hlen1] at hiMax₂
      have hieq : τ₂.vars "i" = xs.length := by omega
      simpa [hieq] using hcollision₂
  refine ⟨τ₂, ?_, hanswer⟩
  have rr := r₀.seq (r₁.seq rloop)
  have rb : Run B detectCollision σ τ₂ (300 * (xs.length + 1)) := by
    simpa [detectCollision, seqs, test, body] using rr.mono (by
      simp [test, Cond.size, Expr.size, σ₁, σ₀]
      omega)
  exact rb

def keyIndex (key : String) : Fin 8 :=
  if key = "key0" then 0 else if key = "key1" then 1 else
  if key = "key2" then 2 else if key = "key3" then 3 else
  if key = "key4" then 4 else if key = "key5" then 5 else
  if key = "key6" then 6 else 7

def digitValue (digits : Fin 8 → ℕ → ℕ) (key : String) (v : ℕ) : ℕ :=
  digits (keyIndex key) v

@[simp] theorem digitValue_keyName (digits : Fin 8 → ℕ → ℕ) (d : Fin 8) :
    digitValue digits (keyName d) = digits d := by
  fin_cases d <;> funext v <;> simp [digitValue, keyIndex, keyName]

theorem mem_keyNames_iff {key : String} :
    key ∈ keyNames ↔ ∃ d : Fin 8, key = keyName d := by
  constructor
  · intro h
    simp [keyNames] at h
    rcases h with h | h | h | h | h | h | h | h
    · exact ⟨0, by simpa [keyName] using h⟩
    · exact ⟨1, by simpa [keyName] using h⟩
    · exact ⟨2, by simpa [keyName] using h⟩
    · exact ⟨3, by simpa [keyName] using h⟩
    · exact ⟨4, by simpa [keyName] using h⟩
    · exact ⟨5, by simpa [keyName] using h⟩
    · exact ⟨6, by simpa [keyName] using h⟩
    · exact ⟨7, by simpa [keyName] using h⟩
  · rintro ⟨d, rfl⟩
    fin_cases d <;> simp [keyNames, keyName]

def AllDigitsEqual (digits : Fin 8 → ℕ → ℕ) (x y : ℕ) : Prop :=
  ∀ d, digits d x = digits d y

instance allDigitsEqualDecidable (digits : Fin 8 → ℕ → ℕ) (x y : ℕ) :
    Decidable (AllDigitsEqual digits x y) := by
  unfold AllDigitsEqual
  infer_instance

theorem equalOn_digitValue_iff (digits : Fin 8 → ℕ → ℕ) (x y : ℕ) :
    EqualOn (digitValue digits) keyNames x y ↔ AllDigitsEqual digits x y := by
  constructor
  · intro h d
    simpa using h (keyName d) (mem_keyNames_iff.mpr ⟨d, rfl⟩)
  · intro h key hkey
    obtain ⟨d, rfl⟩ := mem_keyNames_iff.mp hkey
    simpa using h d

def HasAdjacentEqualDigits (digits : Fin 8 → ℕ → ℕ)
    (xs : List ℕ) : Prop :=
  ∃ j, 1 ≤ j ∧ j < xs.length ∧
    AllDigitsEqual digits (xs.getD (j - 1) 0) (xs.getD j 0)

noncomputable instance hasAdjacentEqualDigitsDecidable (digits : Fin 8 → ℕ → ℕ)
    (xs : List ℕ) : Decidable (HasAdjacentEqualDigits digits xs) :=
  Classical.propDecidable _

theorem adjacentBefore_digitValue_iff (digits : Fin 8 → ℕ → ℕ)
    (xs : List ℕ) :
    AdjacentBefore (digitValue digits) keyNames xs xs.length ↔
      HasAdjacentEqualDigits digits xs := by
  unfold AdjacentBefore HasAdjacentEqualDigits
  apply exists_congr
  intro j
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  exact equalOn_digitValue_iff digits _ _

/-- The concrete detector, specialized to the program's eight arrays. -/
theorem detectCollision_digits_run {B n : ℕ}
    {digits : Fin 8 → ℕ → ℕ} {xs : List ℕ} {ord : ℕ → ℕ} {σ : Env}
    (halen : σ.vars "alen" = xs.length)
    (hord : σ.arrs "ord" = arrOf n ord)
    (hordval : ∀ j < xs.length, ord j = xs.getD j 0)
    (hkeys : ∀ d, σ.arrs (keyName d) = arrOf n (digits d))
    (hvalueB : ∀ d, ∀ i < n, digits d i < B)
    (hvert : ∀ x ∈ xs, x < n) (hxn : xs.length ≤ n)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ', Run B detectCollision σ σ' (300 * (xs.length + 1)) ∧
      σ'.vars "collision" =
        if HasAdjacentEqualDigits digits xs then 1 else 0 := by
  obtain ⟨σ', r, hcollision⟩ := detectCollision_run
    (value := digitValue digits) halen hord hordval
    (fun key hkey => by
      obtain ⟨d, rfl⟩ := mem_keyNames_iff.mp hkey
      simpa using hkeys d)
    (fun key hkey i hi => by
      obtain ⟨d, rfl⟩ := mem_keyNames_iff.mp hkey
      simpa using hvalueB d i hi)
    hvert hxn hnB honeB
  refine ⟨σ', r, ?_⟩
  by_cases h : AdjacentBefore (digitValue digits) keyNames xs xs.length
  · rw [if_pos h] at hcollision
    rw [if_pos ((adjacentBefore_digitValue_iff digits xs).mp h)]
    exact hcollision
  · rw [if_neg h] at hcollision
    rw [if_neg (fun h' => h ((adjacentBefore_digitValue_iff digits xs).mpr h'))]
    exact hcollision

end Lax235315Proofs.Construction.CollisionDetection
