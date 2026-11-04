import Lax185574Proofs.Chain.Ram.DampRam

/-!
The threshold `qOf n r ε` as one command.

The value `qOf n r ε` is the least `q ∈ [1, n + 1]` with
`n ^ a ≤ q ^ c`, where `a = |ε.num|` and `c = 2 r ε.den`, or `n + 1` if
there is none. The powers are far too large for a machine word, so they
are kept as digit arrays in base `β = n + 2` of a fixed length `P`. The
digit `i` of the array sits at position `i` and the array stands for
`Σ_{i < P} d_i β ^ i`. One multiplies such an array by a number below
`β` with a carry loop over all `P` digits, and one compares two arrays
from the top digit down. Every value the command produces stays below
`β ^ 2 + P + a + c` up to a constant.

`qCom` first computes `n ^ a` into `qx` and then scans `q = 1, 2, …, n`
(through `scanFirst`, with `q = w + 1`), computing `q ^ c` into `qy` and
comparing. If no `q ≤ n` passes, the answer is `n + 1` whether or not
`n + 1` passes, so that value is not tested.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

/-! ### Digit values -/

/-- The value of the first `k` digits of `f` in base `β`. -/
def dval (β : ℕ) (f : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ range k, f i * β ^ i

theorem dval_zero (β : ℕ) (f : ℕ → ℕ) : dval β f 0 = 0 := by simp [dval]

theorem dval_succ (β : ℕ) (f : ℕ → ℕ) (k : ℕ) : dval β f (k + 1) = dval β f k + f k * β ^ k :=
  sum_range_succ _ _

theorem dval_congr {β k : ℕ} {f g : ℕ → ℕ} (h : ∀ i < k, f i = g i) : dval β f k = dval β g k :=
  sum_congr rfl fun i hi => by rw [h i (mem_range.1 hi)]

theorem dval_lt {β : ℕ} {f : ℕ → ℕ} : ∀ {k : ℕ}, (∀ i < k, f i < β) → dval β f k < β ^ k
  | 0, _ => by simp [dval]
  | k + 1, hf => by
    have h1 := dval_lt (k := k) fun i hi => hf i (by omega)
    have h2 := hf k (by omega)
    obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
    have h3 : f k * (b + 1) ^ k ≤ b * (b + 1) ^ k := Nat.mul_le_mul_right _ (by omega)
    rw [dval_succ, pow_succ]
    nlinarith

/-- Two digit strings that agree above position `j` and differ at `j`
compare as their digits at `j` do. -/
theorem dval_lt_of_lex {β P j : ℕ} {f g : ℕ → ℕ} (hf : ∀ i < j, f i < β) (hj : j < P)
    (hlt : f j < g j) (hag : ∀ i, j < i → i < P → f i = g i) : dval β f P < dval β g P := by
  have base : dval β f (j + 1) < dval β g (j + 1) := by
    rw [dval_succ, dval_succ]
    have h1 := dval_lt (β := β) hf
    have h2 : (f j + 1) * β ^ j ≤ g j * β ^ j := Nat.mul_le_mul_right _ hlt
    nlinarith
  have key : ∀ k, j + 1 ≤ k → k ≤ P → dval β f k < dval β g k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact base
    | succ k hk ih =>
      intro hkP
      rw [dval_succ, dval_succ, hag k (by omega) (by omega)]
      have := ih (by omega)
      omega
  exact key P (by omega) le_rfl

/-- The array `arr` holds `P` digits below `β` with value `X`. -/
def Digits (τ : Env) (arr : String) (β P X : ℕ) : Prop :=
  ∃ f, Vec τ arr P f ∧ (∀ i < P, f i < β) ∧ dval β f P = X

theorem Digits.of_eq {τ τ' : Env} {arr : String} {β P X : ℕ} (h : Digits τ arr β P X)
    (he : τ'.arrs arr = τ.arrs arr) : Digits τ' arr β P X := by
  obtain ⟨f, hv, hd, hx⟩ := h
  exact ⟨f, hv.of_eq he, hd, hx⟩

theorem Digits.len {τ : Env} {arr : String} {β P X : ℕ} (h : Digits τ arr β P X) :
    (τ.arrs arr).length = P := by
  obtain ⟨f, hv, -, -⟩ := h; exact hv.len

theorem vec_set {τ τ' : Env} {arr : String} {P : ℕ} {f : ℕ → ℕ} (h : Vec τ arr P f) {k v : ℕ}
    (he : τ'.arrs arr = (τ.arrs arr).set k v) :
    Vec τ' arr P (fun i => if i = k then v else f i) := by
  refine ⟨by simp [he, h.len], fun i hi => ?_⟩
  simp only [he, List.getElem?_set, h.get i hi]
  by_cases hik : i = k
  · subst hik; simp [h.len, hi]
  · simp [hik, Ne.symm hik]

/-! ### Setting a digit array to one -/

/-- Set the digit array `arr` (of length `qP`) to the number one. -/
def setOne (arr : String) : Com :=
  .seq (forUp "qi" (.var "qP") (.store arr (.var "qi") (.lit 0))) (.store arr (.lit 0) (.lit 1))

theorem setOne_run {B β P : ℕ} {arr : String} {σ : Env} (hβ : 2 ≤ β) (hP : 1 ≤ P) (hPB : P < B)
    (hσP : σ.vars "qP" = P) (hlen : (σ.arrs arr).length = P) :
    ∃ σ', Run B (setOne arr) σ σ' (P * 11 + 10) ∧ Digits σ' arr β P 1 := by
  let I : ℕ → Env → Prop := fun k τ => (τ.arrs arr).length = P ∧ τ.vars "qP" = P ∧
    ∀ i < k, (τ.arrs arr)[i]? = some 0
  obtain ⟨σ1, hr1, ⟨hl1, hP1, hz1⟩, -⟩ :=
    forUp_run (B := B) (i := "qi") (e := .var "qP") (body := .store arr (.var "qi") (.lit 0))
      (N := P) (K := 3) I hPB
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hI.2.1]; omega), hI.2.1])
      (σ := σ) ⟨hlen, by simp [hσP], fun i hi => by omega⟩
      (by
        rintro k hk τ ⟨hl, hPτ, hz⟩ hik
        refine ⟨_, (Run.store (idx := k) (v := 0) (by rw [evalB_var (by omega), hik])
          (evalB_lit (by omega)) (by omega)).mono (by simp), by simp [hik],
          by simp [hl], by simp [hPτ], fun i hi => ?_⟩
        simp only [arrs_setVar, arrs_setArr, if_true, List.getElem?_set]
        by_cases hik' : k = i
        · subst hik'; simp [hl, hk]
        · simp only [hik', if_false]; exact hz i (by omega))
  refine ⟨σ1.setArr arr 0 1, (Run.seq hr1 (Run.store (idx := 0) (v := 1) (evalB_lit (by omega))
    (evalB_lit (by omega)) (by omega))).mono (by simp), ?_⟩
  refine ⟨fun i => if i = 0 then 1 else 0, ⟨by simp [hl1], fun i hi => ?_⟩,
    fun i hi => by dsimp only; split_ifs <;> omega, ?_⟩
  · simp only [arrs_setArr, if_true, List.getElem?_set]
    by_cases h0 : i = 0
    · subst h0; simp [hl1, hi]
    · simp [h0, Ne.symm h0, hz1 i hi]
  · obtain ⟨P', rfl⟩ : ∃ P', P = P' + 1 := ⟨P - 1, by omega⟩
    clear hr1 hz1 hl1 hP1 hP hPB hσP hlen
    induction P' with
    | zero => simp [dval]
    | succ k ih => rw [dval_succ, ih]; simp

/-! ### Multiplying a digit array by a small number -/

/-- One digit of the multiplication: `v := d_i m + carry`, the digit
becomes `v mod β` and the carry becomes `v / β`. -/
def mulBody (arr : String) : Com :=
  .seq (.assign "qv" (.add (.mul (.get arr (.var "qi")) (.var "qm")) (.var "qcar")))
    (.seq (.assign "qd" (.div (.var "qv") (.var "qb")))
      (.seq (.store arr (.var "qi") (.sub (.var "qv") (.mul (.var "qd") (.var "qb"))))
        (.assign "qcar" (.var "qd"))))

/-- Multiply the digit array `arr` in place by the value of `qm`, in base `qb`. -/
def mulBy (arr : String) : Com :=
  .seq (.assign "qcar" (.lit 0)) (forUp "qi" (.var "qP") (mulBody arr))

theorem mulBody_run {B β P m k : ℕ} {arr : String} {g : ℕ → ℕ} {τ : Env} (hβ : 2 ≤ β)
    (hB : β * β < B) (hk : k < P) (hPB : P < B) (hv : Vec τ arr P g) (hgk : g k < β)
    (hmβ : m < β) (hi : τ.vars "qi" = k) (hb : τ.vars "qb" = β) (hm : τ.vars "qm" = m)
    (hc : τ.vars "qcar" ≤ m) :
    Run B (mulBody arr) τ
      ((((τ.setVar "qv" (g k * m + τ.vars "qcar")).setVar "qd"
        ((g k * m + τ.vars "qcar") / β)).setArr arr k
          ((g k * m + τ.vars "qcar") - (g k * m + τ.vars "qcar") / β * β)).setVar "qcar"
            ((g k * m + τ.vars "qcar") / β)) 20 := by
  set c := τ.vars "qcar" with hcdef
  set v := g k * m + c with hvdef
  have hgm : g k * m ≤ (β - 1) * m := Nat.mul_le_mul_right _ (by omega)
  have hvβ : v ≤ β * m := by
    have : (β - 1) * m + m = β * m := by
      obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
      simp; ring
    omega
  have hβm : β * m < β * β := Nat.mul_lt_mul_of_pos_left hmβ (by omega)
  have hvB : v < B := by omega
  have hβB : β < B := by nlinarith
  have hdv : v / β ≤ v := Nat.div_le_self _ _
  have hdβ : v / β * β ≤ v := Nat.div_mul_le_self _ _
  have e1 : (Expr.add (.mul (.get arr (.var "qi")) (.var "qm")) (.var "qcar")).evalB B τ =
      some v := by
    have := evalB_bin (op := .add) (evalB_bin (op := .mul)
      (evalB_get (B := B) (a := arr) (i := .var "qi") (σ := τ) (k := k) (v := g k)
        (by rw [evalB_var (by omega), hi]) (hv.get k hk) (by omega))
      (evalB_var (x := "qm") (by omega)) (by simp [hm]; omega))
      (evalB_var (x := "qcar") (by omega)) (by simp [hm]; omega)
    simpa only [Bop.apply_add, Bop.apply_mul, hm] using this
  set τ1 := τ.setVar "qv" v
  have e2 : (Expr.div (.var "qv") (.var "qb")).evalB B τ1 = some (v / β) := by
    have := evalB_bin (op := .div) (evalB_var (B := B) (x := "qv") (σ := τ1) (by simp [τ1]; omega))
      (evalB_var (x := "qb") (by simp [τ1, hb]; omega)) (by simp [τ1, hb]; omega)
    simp only [Bop.apply_div, τ1, vars_setVar, if_true, hb,
      if_neg (show "qb" ≠ "qv" by decide)] at this
    exact this
  set τ2 := τ1.setVar "qd" (v / β)
  have e3 : (Expr.sub (.var "qv") (.mul (.var "qd") (.var "qb"))).evalB B τ2 =
      some (v - v / β * β) := by
    have := evalB_bin (op := .sub) (evalB_var (B := B) (x := "qv") (σ := τ2) (by simp [τ2, τ1]; omega))
      (evalB_bin (op := .mul) (evalB_var (x := "qd") (by simp [τ2]; omega))
        (evalB_var (x := "qb") (by simp [τ2, τ1, hb]; omega)) (by simp [τ2, τ1, hb]; omega))
      (by simp [τ2, τ1, hb]; omega)
    simp only [Bop.apply_sub, Bop.apply_mul, τ1, τ2, vars_setVar, if_true, hb,
      if_neg (show "qv" ≠ "qd" by decide), if_neg (show "qb" ≠ "qd" by decide),
      if_neg (show "qb" ≠ "qv" by decide)] at this
    exact this
  set τ3 := τ2.setArr arr k (v - v / β * β)
  have h1 := Run.assign (B := B) (x := "qv") e1
  have h2 := Run.assign (B := B) (x := "qd") e2
  have h3 := Run.store (B := B) (a := arr) (i := .var "qi") (σ := τ2) (idx := k)
    (by rw [evalB_var (by simp [τ2, τ1, hi]; omega)]; simp [τ2, τ1, hi]) e3
    (by simp [τ2, τ1, hv.len, hk])
  have h4 := Run.assign (B := B) (x := "qcar") (σ := τ3) (e := .var "qd") (v := v / β)
    (by rw [evalB_var (by simp [τ3, τ2]; omega)]; simp [τ3, τ2])
  exact (Run.seq h1 (Run.seq h2 (Run.seq h3 h4))).mono (by simp)

/-- The digit after one step of the multiplication is below `β`, and the
step adds up. -/
theorem mul_digit_step {β m d c : ℕ} (hβ : 2 ≤ β) :
    (d * m + c) - (d * m + c) / β * β < β ∧
      (d * m + c) - (d * m + c) / β * β + β * ((d * m + c) / β) = d * m + c := by
  have h1 := Nat.div_add_mod (d * m + c) β
  have h2 := Nat.mod_lt (d * m + c) (show β > 0 by omega)
  have h3 : (d * m + c) / β * β = β * ((d * m + c) / β) := Nat.mul_comm _ _
  constructor <;> omega

theorem mulBy_run {B β P m X : ℕ} {arr : String} {σ : Env} (hβ : 2 ≤ β) (hB : β * β < B)
    (hPB : P < B) (hmβ : m < β) (hov : m * X < β ^ P) (hb : σ.vars "qb" = β)
    (hm : σ.vars "qm" = m) (hP : σ.vars "qP" = P) (hd : Digits σ arr β P X) :
    ∃ σ', Run B (mulBy arr) σ σ' (P * 28 + 8) ∧ Digits σ' arr β P (m * X) := by
  obtain ⟨f, hvf, hdf, rfl⟩ := hd
  let I : ℕ → Env → Prop := fun k τ => τ.vars "qb" = β ∧ τ.vars "qm" = m ∧ τ.vars "qP" = P ∧
    τ.vars "qcar" ≤ m ∧ ∃ g, Vec τ arr P g ∧ (∀ i < P, g i < β) ∧
      (∀ i, k ≤ i → i < P → g i = f i) ∧ dval β g k + τ.vars "qcar" * β ^ k = m * dval β f k
  obtain ⟨σ1, hr1, ⟨hb1, hm1, hP1, hc1, g, hvg, hdg, -, heq⟩, -⟩ :=
    forUp_run (B := B) (i := "qi") (e := .var "qP") (body := mulBody arr) (N := P) (K := 20) I hPB
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hI.2.2.1]; omega), hI.2.2.1])
      (σ := σ.setVar "qcar" 0)
      ⟨by simp [hb], by simp [hm], by simp [hP], by simp,
        f, hvf.of_eq rfl, hdf, fun i _ _ => rfl, by simp [dval_zero]⟩
      (by
        rintro k hk τ ⟨hbτ, hmτ, hPτ, hcτ, g, hvg, hdg, hag, heq⟩ hik
        have hgk : g k = f k := hag k le_rfl hk
        refine ⟨_, mulBody_run hβ hB hk hPB hvg (hdg k hk) hmβ hik hbτ hmτ hcτ, by simp [hik],
          by simp [hbτ], by simp [hmτ], by simp [hPτ], ?_, ?_⟩
        · simp only [vars_setVar, if_true, if_neg (show "qcar" ≠ "qi" by decide)]
          apply Nat.div_le_of_le_mul
          have hgm : g k * m ≤ (β - 1) * m := Nat.mul_le_mul_right _ (by have := hdg k hk; omega)
          have : (β - 1) * m + m = β * m := by
            obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
            simp; ring
          omega
        · set c := τ.vars "qcar"
          obtain ⟨hlt, hsplit⟩ := mul_digit_step (d := g k) (m := m) (c := c) hβ
          set r := (g k * m + c) - (g k * m + c) / β * β
          set d := (g k * m + c) / β
          refine ⟨fun i => if i = k then r else g i, vec_set hvg (by simp), fun i hi => ?_,
            fun i hi1 hi2 => ?_, ?_⟩
          · dsimp only; split_ifs
            · exact hlt
            · exact hdg i hi
          · dsimp only; rw [if_neg (by omega)]; exact hag i (by omega) hi2
          · simp only [vars_setVar, if_true, if_neg (show "qcar" ≠ "qi" by decide)]
            have hcg : dval β (fun i => if i = k then r else g i) k = dval β g k :=
              dval_congr fun i hi => by rw [if_neg (by omega)]
            rw [dval_succ, hcg, dval_succ, if_pos rfl, pow_succ, ← hgk]
            have : r * β ^ k + d * (β ^ k * β) = (g k * m + c) * β ^ k := by
              rw [← hsplit]; ring
            nlinarith)
  refine ⟨σ1, ?_, g, hvg, hdg, ?_⟩
  · unfold mulBy
    exact (Run.seq (Run.assign (v := 0) (by simp; omega)) hr1).mono (by simp; omega)
  have hc0 : σ1.vars "qcar" = 0 := by
    by_contra h
    have : β ^ P ≤ σ1.vars "qcar" * β ^ P := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · rw [hc0] at heq; simpa using heq

/-! ### Powers -/

/-- Set the digit array `arr` to `m ^ E`, where `m` is the value of `e`
and `E` the value of the scalar `ex`. -/
def powCom (arr : String) (e : Expr) (ex : String) : Com :=
  .seq (.assign "qm" e) (.seq (setOne arr) (forUp "qj" (.var ex) (mulBy arr)))

theorem setOne_wvars (arr : String) : (setOne arr).wvars = ["qi", "qi"] := rfl

theorem mulBy_wvars (arr : String) :
    (mulBy arr).wvars = ["qcar", "qi", "qv", "qd", "qcar", "qi"] := rfl

theorem powCom_run {B β P m E : ℕ} {arr ex : String} {e : Expr} {σ : Env} (hβ : 2 ≤ β)
    (hB : β * β < B) (hPB : P < B) (hEP : E < P) (hmβ : m < β) (he : e.evalB B σ = some m)
    (hes : e.size ≤ 3) (hb : σ.vars "qb" = β) (hP : σ.vars "qP" = P) (hE : σ.vars ex = E)
    (hex : ex ∉ ["qm", "qi", "qcar", "qv", "qd", "qj"]) (hlen : (σ.arrs arr).length = P) :
    ∃ σ', Run B (powCom arr e ex) σ σ' ((E + 1) * (P * 30 + 30)) ∧ Digits σ' arr β P (m ^ E) := by
  have hex' : ∀ y ∈ ["qm", "qi", "qcar", "qv", "qd", "qj"], ex ≠ y := fun y hy h => hex (h ▸ hy)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hex'
  set σ1 := σ.setVar "qm" m
  obtain ⟨σ2, hr2, hd2⟩ := setOne_run (B := B) (β := β) (arr := arr) (σ := σ1) hβ (by omega) hPB
    (by simp [σ1, hP]) (by simp [σ1, hlen])
  have hf2 : ∀ y, y ≠ "qi" → σ2.vars y = σ1.vars y := fun y hy =>
    hr2.frame_var y (by rw [setOne_wvars]; simp [hy])
  let I : ℕ → Env → Prop := fun j τ => τ.vars "qb" = β ∧ τ.vars "qm" = m ∧ τ.vars "qP" = P ∧
    τ.vars ex = E ∧ Digits τ arr β P (m ^ j)
  have hfx : ∀ y, y ∉ (mulBy arr).wvars → y ≠ "qj" → ∀ τ τ' K j, Run B (mulBy arr) τ τ' K →
      (τ'.setVar "qj" j).vars y = τ.vars y := fun y hy hj τ τ' K j hr => by
    simp [hj, hr.frame_var y hy]
  obtain ⟨σ3, hr3, ⟨-, -, -, -, hd3⟩, -⟩ :=
    forUp_run (B := B) (i := "qj") (e := .var ex) (body := mulBy arr) (N := E) (K := P * 28 + 8) I
      (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hI.2.2.2.1]; omega), hI.2.2.2.1])
      (σ := σ2)
      ⟨by simp [hf2, σ1, hb], by simp [hf2, σ1], by simp [hf2, σ1, hP],
        by simp [hf2 ex hex'.2.1, σ1, hex'.1, hE, hex'.2.2.2.2.2], hd2.of_eq rfl⟩
      (by
        rintro j hj τ ⟨hbτ, hmτ, hPτ, hEτ, hdτ⟩ hij
        have hov : m * m ^ j < β ^ P := by
          rw [← pow_succ']
          calc m ^ (j + 1) ≤ β ^ (j + 1) := Nat.pow_le_pow_left (by omega) _
            _ < β ^ P := Nat.pow_lt_pow_right (by omega) (by omega)
        obtain ⟨τ', hr, hd'⟩ := mulBy_run hβ hB hPB hmβ hov hbτ hmτ hPτ hdτ
        have hw : ∀ y, y ∉ (mulBy arr).wvars → y ≠ "qj" → (τ'.setVar "qj" (j + 1)).vars y = τ.vars y :=
          fun y hy hj => hfx y hy hj τ τ' _ _ hr
        refine ⟨τ', hr, by rw [hr.frame_var "qj" (by rw [mulBy_wvars]; decide), hij], ?_, ?_, ?_,
          ?_, ?_⟩
        · rw [hw "qb" (by rw [mulBy_wvars]; decide) (by decide), hbτ]
        · rw [hw "qm" (by rw [mulBy_wvars]; decide) (by decide), hmτ]
        · rw [hw "qP" (by rw [mulBy_wvars]; decide) (by decide), hPτ]
        · rw [hw ex (by rw [mulBy_wvars]; simp [hex'.2.1, hex'.2.2.1, hex'.2.2.2.1,
            hex'.2.2.2.2.1]) hex'.2.2.2.2.2, hEτ]
        · rw [pow_succ']
          exact hd'.of_eq rfl)
  refine ⟨σ3, ?_, hd3⟩
  unfold powCom
  refine (Run.seq (Run.assign he) (Run.seq hr2 hr3)).mono ?_
  simp only [size_var]
  nlinarith

/-! ### Comparing two digit arrays -/

/-- One step of the comparison: move down one digit, and stop with the
verdict in `qle` at the first digit where `qx` and `qy` differ. -/
def cmpBody : Com :=
  .seq (.assign "qi" (.sub (.var "qi") (.lit 1)))
    (.ite (.eq (.get "qx" (.var "qi")) (.get "qy" (.var "qi"))) .skip
      (.seq (.ite (.lt (.get "qx" (.var "qi")) (.get "qy" (.var "qi"))) (.assign "qle" (.lit 1))
          (.assign "qle" (.lit 0)))
        (.assign "qi" (.lit 0))))

/-- Compare the digit arrays `qx` and `qy` (of length `qP`) from the top
digit down, leaving `1` in `qle` if the value of `qx` is at most that of
`qy` and `0` otherwise. -/
def cmpCom : Com :=
  .seq (.assign "qi" (.var "qP")) (.seq (.assign "qle" (.lit 1))
    (.while (.lt (.lit 0) (.var "qi")) cmpBody))

theorem cmpBody_run {B β P k : ℕ} {fx fy : ℕ → ℕ} {τ : Env} (hβB : β < B) (hPB : P < B)
    (hk : k < P) (hi : τ.vars "qi" = k + 1) (hvx : Vec τ "qx" P fx) (hvy : Vec τ "qy" P fy)
    (hdx : ∀ i < P, fx i < β) (hdy : ∀ i < P, fy i < β) :
    ∃ τ', Run B cmpBody τ τ' 20 ∧ τ'.arrs = τ.arrs ∧
      ((fx k = fy k ∧ τ'.vars "qi" = k ∧ τ'.vars "qle" = τ.vars "qle") ∨
        (fx k ≠ fy k ∧ τ'.vars "qi" = 0 ∧ τ'.vars "qle" = ind (fx k < fy k))) := by
  set τ1 := τ.setVar "qi" k
  have h1 : Run B (.assign "qi" (.sub (.var "qi") (.lit 1))) τ τ1 4 := by
    refine (Run.assign (v := k) ?_).mono (by simp)
    have := evalB_bin (op := .sub) (evalB_var (B := B) (x := "qi") (σ := τ) (by omega))
      (evalB_lit (n := 1) (by omega)) (by simp [hi]; omega)
    simpa [hi] using this
  have hq : (Expr.var "qi").evalB B τ1 = some k := by
    rw [evalB_var (by simp [τ1]; omega)]; simp [τ1]
  have gx : (Expr.get "qx" (.var "qi")).evalB B τ1 = some (fx k) :=
    evalB_get hq (hvx.get k hk) (by have := hdx k hk; omega)
  have gy : (Expr.get "qy" (.var "qi")).evalB B τ1 = some (fy k) :=
    evalB_get hq (hvy.get k hk) (by have := hdy k hk; omega)
  have hc1 := evalB_condEq' gx gy
  have hc2 := evalB_condLt gx gy
  by_cases heq : fx k = fy k
  · refine ⟨τ1, ?_, rfl, Or.inl ⟨heq, by simp [τ1], by simp [τ1]⟩⟩
    unfold cmpBody
    exact (Run.seq h1 (Run.ite_true (by rw [hc1]; simp [heq]) Run.skip)).mono (by simp)
  · by_cases hlt : fx k < fy k
    · refine ⟨(τ1.setVar "qle" 1).setVar "qi" 0, ?_, rfl,
        Or.inr ⟨heq, by simp, by simp [ind, hlt]⟩⟩
      unfold cmpBody
      exact (Run.seq h1 (Run.ite_false (by rw [hc1]; simp [heq])
        (Run.seq (Run.ite_true (by rw [hc2]; simp [hlt]) (Run.assign (v := 1) (by simp; omega)))
          (Run.assign (v := 0) (by simp; omega))))).mono (by simp)
    · refine ⟨(τ1.setVar "qle" 0).setVar "qi" 0, ?_, rfl,
        Or.inr ⟨heq, by simp, by simp [ind, hlt]⟩⟩
      unfold cmpBody
      exact (Run.seq h1 (Run.ite_false (by rw [hc1]; simp [heq])
        (Run.seq (Run.ite_false (by rw [hc2]; simp [hlt]) (Run.assign (v := 0) (by simp; omega)))
          (Run.assign (v := 0) (by simp; omega))))).mono (by simp)

theorem cmpCom_run {B β P X Y : ℕ} {σ : Env} (hβ : 2 ≤ β) (hβB : β < B) (hPB : P < B)
    (hP : σ.vars "qP" = P) (hx : Digits σ "qx" β P X) (hy : Digits σ "qy" β P Y) :
    ∃ σ', Run B cmpCom σ σ' (P * 30 + 10) ∧ σ'.vars "qle" = ind (X ≤ Y) ∧ σ'.arrs = σ.arrs := by
  obtain ⟨fx, hvx, hdx, rfl⟩ := hx
  obtain ⟨fy, hvy, hdy, rfl⟩ := hy
  set σ0 := (σ.setVar "qi" P).setVar "qle" 1
  let J : Env → Prop := fun τ => τ.arrs = σ.arrs ∧ τ.vars "qi" ≤ P ∧
    (((∀ i, τ.vars "qi" ≤ i → i < P → fx i = fy i) ∧ τ.vars "qle" = 1) ∨
      (τ.vars "qi" = 0 ∧ τ.vars "qle" = ind (dval β fx P ≤ dval β fy P)))
  have hb : ∀ τ : Env, τ.vars "qi" < B →
      (Cond.lt (.lit 0) (.var "qi")).evalB B τ = some (decide (0 < τ.vars "qi")) := fun τ h =>
    evalB_condLt (evalB_lit (by omega)) (evalB_var h)
  obtain ⟨σ', hr, ⟨ha', hi', hst'⟩, hf'⟩ :=
    Run.while_count (B := B) (b := .lt (.lit 0) (.var "qi")) (c := cmpBody) J
      (fun τ => τ.vars "qi") 20
      (fun τ hJ => ⟨_, hb τ (by have := hJ.2.1; omega)⟩)
      (by
        rintro τ ⟨ha, hiP, hst⟩ hc
        rw [hb τ (by omega)] at hc
        simp only [Option.some.injEq, decide_eq_true_eq] at hc
        obtain ⟨k, hk⟩ : ∃ k, τ.vars "qi" = k + 1 := ⟨τ.vars "qi" - 1, by omega⟩
        obtain ⟨τ', hr, ha', hcase⟩ := cmpBody_run (k := k) hβB hPB (by omega) hk
          (hvx.of_eq (by rw [ha])) (hvy.of_eq (by rw [ha])) hdx hdy
        refine ⟨τ', hr, ⟨by rw [ha', ha], ?_, ?_⟩, ?_⟩
        · rcases hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
        · rcases hst with ⟨hag, hle⟩ | ⟨h0, -⟩
          · rcases hcase with ⟨he, h1, h2⟩ | ⟨hne, h1, h2⟩
            · left
              refine ⟨fun i hi1 hi2 => ?_, by rw [h2, hle]⟩
              rcases Nat.lt_or_ge i (k + 1) with h | h
              · have : i = k := by omega
                subst this; exact he
              · exact hag i (by omega) hi2
            · right
              refine ⟨h1, ?_⟩
              rw [h2, ind_eq_iff]
              have hag' : ∀ i, k < i → i < P → fx i = fy i := fun i h1 h2 => hag i (by omega) h2
              constructor
              · intro h
                exact (dval_lt_of_lex (fun i _ => hdx i (by omega)) (by omega) h hag').le
              · intro h
                rcases Nat.lt_or_gt_of_ne hne with h3 | h3
                · exact h3
                · exact absurd (dval_lt_of_lex (fun i _ => hdy i (by omega)) (by omega) h3
                    (fun i h1 h2 => (hag' i h1 h2).symm)) (by omega)
          · omega
        · rcases hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega)
      (show J σ0 by
        refine ⟨rfl, by simp [σ0], Or.inl ⟨fun i h1 h2 => ?_, by simp [σ0]⟩⟩
        simp [σ0] at h1; omega)
  have hi0 : σ'.vars "qi" = 0 := by
    rw [hb σ' (by omega)] at hf'
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hf'
    omega
  refine ⟨σ', ?_, ?_, by rw [ha']⟩
  · unfold cmpCom
    refine (Run.seq (Run.assign (v := P) (by simp [hP]; omega))
      (Run.seq (Run.assign (v := 1) (by simp; omega)) hr)).mono ?_
    simp [σ0]
    omega
  · rcases hst' with ⟨hag, hle⟩ | ⟨-, h⟩
    · rw [hle, eq_comm, ind_eq_one, dval_congr fun i hi => hag i (by omega) hi]
    · exact h

/-! ### The threshold -/

/-- Test the candidate `q = w + 1`: compute `q ^ c` into `qy` (with `c`
in `qc`), compare it with `qx`, and leave the verdict in `ok`. -/
def qTest : Com :=
  .seq (powCom "qy" (.add (.var "w") (.lit 1)) "qc") (.seq cmpCom (.assign "ok" (.var "qle")))

/-- The threshold: with `n`, `a` and `c` in `n`, `qa` and `qc`, and the
digit length in `qP`, leave in `q` the least `q ∈ [1, n + 1]` with
`n ^ a ≤ q ^ c`, or `n + 1` if there is none. -/
def qCom : Com :=
  .seq (.assign "qb" (.add (.var "n") (.lit 2)))
    (.seq (powCom "qx" (.var "n") "qa")
      (.seq (scanFirst qTest) (.assign "q" (.add (.var "fw") (.lit 1)))))

theorem qTest_wvars : qTest.wvars = ["qm", "qi", "qi", "qj", "qcar", "qi", "qv", "qd", "qcar",
    "qi", "qj", "qi", "qle", "qi", "qle", "qle", "qi", "ok"] := rfl

/-- The scalars `qCom` may write. -/
def qWritten : List String := ["qb", "qm", "qi", "qj", "qcar", "qv", "qd", "qle", "ok", "w", "fw", "q"]

theorem qCom_wvars : qCom.wvars = ["qb", "qm", "qi", "qi", "qj", "qcar", "qi", "qv", "qd", "qcar",
    "qi", "qj", "w", "fw", "qm", "qi", "qi", "qj", "qcar", "qi", "qv", "qd", "qcar", "qi", "qj",
    "qi", "qle", "qi", "qle", "qle", "qi", "ok", "fw", "w", "w", "q"] := rfl

/-- What holds throughout the scan over the candidates. -/
def QInv (n a c P : ℕ) (τ : Env) : Prop :=
  τ.vars "n" = n ∧ τ.vars "qb" = n + 2 ∧ τ.vars "qP" = P ∧ τ.vars "qc" = c ∧
    Digits τ "qx" (n + 2) P (n ^ a) ∧ (τ.arrs "qy").length = P

theorem qTest_run {B n a c P k : ℕ} {τ : Env} (hB : (n + 2) * (n + 2) + P + a + c + 10 < B)
    (hcP : c < P) (hI : QInv n a c P τ) (hw : τ.vars "w" = k) (hk : k < n) :
    ∃ τ', Run B qTest τ τ' ((c + 2) * (P * 30 + 30)) ∧ QInv n a c P τ' ∧ τ'.vars "w" = k ∧
      τ'.vars "fw" = τ.vars "fw" ∧ τ'.vars "ok" = ind (n ^ a ≤ (k + 1) ^ c) := by
  obtain ⟨hn, hb, hP, hc, hx, hy⟩ := hI
  have hβ : 2 ≤ n + 2 := by omega
  have hnB : n + 2 < B := by nlinarith
  obtain ⟨τ1, hr1, hd1⟩ := powCom_run (B := B) (β := n + 2) (P := P) (m := k + 1) (E := c)
    (arr := "qy") (ex := "qc") (e := .add (.var "w") (.lit 1)) (σ := τ) hβ (by omega) (by omega)
    hcP (by omega)
    (by
      have := evalB_bin (op := .add) (evalB_var (B := B) (x := "w") (σ := τ) (by omega))
        (evalB_lit (n := 1) (by omega)) (by simp [hw]; omega)
      simpa [hw] using this)
    (by simp) hb hP hc (by decide) hy
  have hx1 : Digits τ1 "qx" (n + 2) P (n ^ a) := hx.of_eq (hr1.frame_arr "qx" (by decide))
  obtain ⟨τ2, hr2, hle2, ha2⟩ := cmpCom_run (B := B) hβ (by nlinarith) (by omega)
    (by rw [hr1.frame_var "qP" (by decide), hP]) hx1 hd1
  have hr : Run B qTest τ (τ2.setVar "ok" (ind (n ^ a ≤ (k + 1) ^ c))) ((c + 2) * (P * 30 + 30)) := by
    unfold qTest
    refine (Run.seq hr1 (Run.seq hr2 (Run.assign ?_))).mono ?_
    · rw [evalB_var (by rw [hle2]; have := ind_le_one (n ^ a ≤ (k + 1) ^ c); omega), hle2]
    · simp only [size_var]; nlinarith
  have hfr : ∀ y, y ∉ qTest.wvars → (τ2.setVar "ok" (ind (n ^ a ≤ (k + 1) ^ c))).vars y = τ.vars y :=
    fun y hy => hr.frame_var y hy
  refine ⟨_, hr, ⟨by rw [hfr "n" (by rw [qTest_wvars]; decide), hn],
    by rw [hfr "qb" (by rw [qTest_wvars]; decide), hb],
    by rw [hfr "qP" (by rw [qTest_wvars]; decide), hP],
    by rw [hfr "qc" (by rw [qTest_wvars]; decide), hc], hx1.of_eq (by simp [ha2]),
    by simp [ha2, hd1.len]⟩,
    by rw [hfr "w" (by rw [qTest_wvars]; decide), hw],
    hfr "fw" (by rw [qTest_wvars]; decide), by simp⟩

/-- The scan over `w < n` finds the threshold. -/
theorem firstN_getD_succ (n a c : ℕ) :
    (firstN n (fun w => n ^ a ≤ (w + 1) ^ c)).getD n + 1 =
      (firstFrom (fun q => decide (n ^ a ≤ q ^ c)) 1 (n + 1)).getD (n + 1) := by
  cases h : firstN n (fun w => n ^ a ≤ (w + 1) ^ c) with
  | some w =>
    obtain ⟨hw, hp, hmin⟩ := firstN_eq_some.1 h
    rw [firstFrom_eq_some_of (a := w + 1) (by omega) (by omega) (by simpa using hp)
      (fun b hb1 hb2 => by
        have := hmin (b - 1) (by omega)
        rw [show b - 1 + 1 = b by omega] at this
        simpa using this)]
    rfl
  | none =>
    have hall := firstN_eq_none.1 h
    have hb : ∀ b, 1 ≤ b → b < 1 + n → decide (n ^ a ≤ b ^ c) = false := fun b hb1 hb2 => by
      have := hall (b - 1) (by omega)
      rw [show b - 1 + 1 = b by omega] at this
      simpa using this
    by_cases hl : n ^ a ≤ (n + 1) ^ c
    · rw [firstFrom_eq_some_of (a := n + 1) (by omega) (by omega) (by simpa using hl)
        (fun b hb1 hb2 => hb b hb1 (by omega))]
      rfl
    · rw [firstFrom_eq_none_of (fun b hb1 hb2 => by
        rcases Nat.lt_or_ge b (1 + n) with h' | h'
        · exact hb b hb1 h'
        · rw [show b = n + 1 by omega]; simpa using hl)]
      rfl

/-- The cost bound of `qCom`. -/
def qCost (n a c P : ℕ) : ℕ :=
  n * ((c + 2) * (P * 30 + 30) + 20) + (a + 1) * (P * 30 + 30) + 40

/-- **The threshold as one command.** With `n`, `a`, `c` and `P` in the
scalars `n`, `qa`, `qc` and `qP`, where `a + c + 2 ≤ P`, and the arrays
`qx` and `qy` of length `P`, the command `qCom` leaves in `q` the least
`q ∈ [1, n + 1]` with `n ^ a ≤ q ^ c`, or `n + 1` if there is none. It
writes only the scalars of `qWritten` and the arrays `qx` and `qy`, and
it does not touch the tapes. -/
theorem qCom_run {B n a c P : ℕ} {σ : Env} (hn : σ.vars "n" = n) (ha : σ.vars "qa" = a)
    (hc : σ.vars "qc" = c) (hP : σ.vars "qP" = P) (hPac : a + c + 2 ≤ P)
    (hx : (σ.arrs "qx").length = P) (hy : (σ.arrs "qy").length = P)
    (hB : (n + 2) * (n + 2) + P + a + c + 10 < B) :
    ∃ σ', Run B qCom σ σ' (qCost n a c P) ∧
      σ'.vars "q" = (firstFrom (fun q => decide (n ^ a ≤ q ^ c)) 1 (n + 1)).getD (n + 1) ∧
      (∀ x, x ∉ qWritten → σ'.vars x = σ.vars x) ∧
      (∀ arr, arr ∉ ["qx", "qy"] → σ'.arrs arr = σ.arrs arr) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  have hβ : 2 ≤ n + 2 := by omega
  have hnB : n + 2 < B := by nlinarith
  set σ0 := σ.setVar "qb" (n + 2)
  have h0 : Run B (.assign "qb" (.add (.var "n") (.lit 2))) σ σ0 4 := by
    refine (Run.assign ?_).mono (by simp)
    have := evalB_bin (op := .add) (evalB_var (B := B) (x := "n") (σ := σ) (by omega))
      (evalB_lit (n := 2) (by omega)) (by simp [hn]; omega)
    simpa [hn] using this
  obtain ⟨σ1, hr1, hd1⟩ := powCom_run (B := B) (β := n + 2) (P := P) (m := n) (E := a)
    (arr := "qx") (ex := "qa") (e := .var "n") (σ := σ0) hβ (by omega) (by omega)
    (by omega) (by omega) (by rw [evalB_var (by simp [σ0, hn]; omega)]; simp [σ0, hn])
    (by simp) (by simp [σ0]) (by simp [σ0, hP]) (by simp [σ0, ha]) (by decide) (by simp [σ0, hx])
  have hf1 : ∀ y, y ∉ (powCom "qx" (.var "n") "qa").wvars → σ1.vars y = σ0.vars y :=
    fun y hy => hr1.frame_var y hy
  have hI1 : QInv n a c P σ1 := by
    refine ⟨by rw [hf1 "n" (by decide)]; simp [σ0, hn], by rw [hf1 "qb" (by decide)]; simp [σ0],
      by rw [hf1 "qP" (by decide)]; simp [σ0, hP], by rw [hf1 "qc" (by decide)]; simp [σ0, hc],
      hd1, ?_⟩
    rw [hr1.frame_arr "qy" (by decide)]; simpa [σ0] using hy
  obtain ⟨σ2, K2, hr2, hI2, hfw2, hK2⟩ := scanFirst_run (B := B) (n := n)
    (Kt := (c + 2) * (P * 30 + 30)) (tst := qTest) (QInv n a c P) (fun _ => 0)
    (fun w => n ^ a ≤ (w + 1) ^ c) (by nlinarith) (fun τ h => h.1)
    (fun τ x ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4],
      h5.of_eq rfl, by simp [h6]⟩)
    (fun τ x ⟨h1, h2, h3, h4, h5, h6⟩ => ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4],
      h5.of_eq rfl, by simp [h6]⟩)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun τ k hI hw hk => by
      obtain ⟨τ', hr, hI', hw', hf', hok'⟩ := qTest_run hB (by omega) hI hw hk
      exact ⟨τ', _, hr, hI', hw', hf', hok', by omega⟩)
    hI1
  have hfwB : σ2.vars "fw" ≤ n := by
    rw [hfw2]
    cases h : firstN n (fun w => n ^ a ≤ (w + 1) ^ c) with
    | none => simp
    | some w => have := (firstN_eq_some.1 h).1; simp; omega
  have hr : Run B qCom σ (σ2.setVar "q" (σ2.vars "fw" + 1)) (qCost n a c P) := by
    unfold qCom
    refine (Run.seq h0 (Run.seq hr1 (Run.seq hr2 (Run.assign ?_)))).mono ?_
    · have := evalB_bin (op := .add) (evalB_var (B := B) (x := "fw") (σ := σ2) (by omega))
        (evalB_lit (n := 1) (by omega)) (by simp; omega)
      simpa using this
    · unfold qCost; simp only [size_var, size_add, size_lit]; nlinarith
  refine ⟨_, hr, by simp [hfw2, firstN_getD_succ], fun x hx => hr.frame_var x ?_,
    fun arr harr => hr.frame_arr arr ?_, hr.frame_inp (by decide), hr.out_eq (by decide)⟩
  · intro hm
    rw [qCom_wvars] at hm
    apply hx
    simp only [qWritten]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]
  · intro hm; apply harr
    have : qCom.warrs = ["qx", "qx", "qx", "qy", "qy", "qy"] := rfl
    rw [this] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with h | h | h | h | h | h <;> simp [h]

end Lax185574Proofs.Chain.Ram
