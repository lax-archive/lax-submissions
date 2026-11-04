import Lax185574Proofs.Chain.Ram.BigBits
import Lax185574Proofs.Chain.Welzl

/-!
The greedy procedure of the Welzl ordering as a program, first part:
frames, counting loops of varying cost, crossing on numbers, and the
update of all values `ξ(u,v)` for one vertex `x`.

The values `ξ(u,v)` for all `u, v < n` are binary big numbers (see
`BigBits`) with index `u * n + v` and `D = 2n + 2` bits each. The weight
of `x` is `2 ^ wc[x]`. The command `updX` adds `2 ^ wc[x]` to `ξ(u,v)`
for every pair `u v` crossed by the vertex `x` in the scalar `wx`
(`updX_run`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

/-! ### Frames -/

/-- From `σ` to `τ` only the scalars in `W` and the arrays in `Wa` may
have changed. -/
structure Fr (W Wa : List String) (σ τ : Env) : Prop where
  vars : ∀ y, y ∉ W → τ.vars y = σ.vars y
  arrs : ∀ a, a ∉ Wa → τ.arrs a = σ.arrs a
  inp : τ.inp = σ.inp
  out : τ.out = σ.out

theorem Fr.refl (W Wa : List String) (σ : Env) : Fr W Wa σ σ :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Fr.trans {W Wa : List String} {σ τ ρ : Env} (h : Fr W Wa σ τ) (h' : Fr W Wa τ ρ) :
    Fr W Wa σ ρ :=
  ⟨fun y hy => (h'.vars y hy).trans (h.vars y hy), fun a ha => (h'.arrs a ha).trans (h.arrs a ha),
    h'.inp.trans h.inp, h'.out.trans h.out⟩

theorem Fr.mono {W Wa W' Wa' : List String} {σ τ : Env} (h : Fr W Wa σ τ) (hW : W ⊆ W')
    (hA : Wa ⊆ Wa') : Fr W' Wa' σ τ :=
  ⟨fun y hy => h.vars y (fun m => hy (hW m)), fun a ha => h.arrs a (fun m => ha (hA m)),
    h.inp, h.out⟩

theorem Fr.setVar {W Wa : List String} {σ τ : Env} (h : Fr W Wa σ τ) {y : String} (hy : y ∈ W)
    (v : ℕ) : Fr W Wa σ (τ.setVar y v) :=
  ⟨fun z hz => by
    rw [vars_setVar, if_neg (fun (e : z = y) => hz (e ▸ hy))]; exact h.vars z hz,
    fun a ha => h.arrs a ha, h.inp, h.out⟩

theorem Fr.setArr {W Wa : List String} {σ τ : Env} (h : Fr W Wa σ τ) {a : String} (ha : a ∈ Wa)
    (i v : ℕ) : Fr W Wa σ (τ.setArr a i v) :=
  ⟨fun z hz => h.vars z hz, fun b hb => by
    rw [arrs_setArr, if_neg (fun (e : b = a) => hb (e ▸ ha))]; exact h.arrs b hb, h.inp, h.out⟩

/-! ### Counting loops whose rounds have different costs -/

/-- **The counting loop rule with varying costs.** Round `k` costs at
most `c k`. -/
theorem forUpV_run {B : ℕ} {i : String} {e : Expr} {body : Com} {N : ℕ} (c : ℕ → ℕ)
    (I : ℕ → Env → Prop) {σ : Env} (hN : N < B)
    (he : ∀ k ≤ N, ∀ τ, I k τ → τ.vars i = k → e.evalB B τ = some N)
    (h0 : I 0 (σ.setVar i 0))
    (hstep : ∀ k < N, ∀ τ, I k τ → τ.vars i = k →
      ∃ τ', Run B body τ τ' (c k) ∧ τ'.vars i = k ∧ I (k + 1) (τ'.setVar i (k + 1))) :
    ∃ σ', Run B (forUp i e body) σ σ' (∑ k ∈ range N, (c k + e.size + 7) + e.size + 5) ∧
      I N σ' ∧ σ'.vars i = N := by
  let J : Env → Prop := fun τ => ∃ k ≤ N, τ.vars i = k ∧ I k τ
  let Φ : Env → ℕ := fun τ => ∑ k ∈ Ico (τ.vars i) N, (c k + e.size + 7)
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
        refine ⟨τ'.setVar i (k + 1), _, Run.seq hr (Run.assign (v := k + 1) ?_),
          ⟨k + 1, hkN, by simp, hI'⟩, ?_⟩
        · simp [hi']; omega
        · simp only [Φ, vars_setVar, if_true, hik]
          rw [Finset.sum_eq_sum_Ico_succ_bot hkN]
          simp only [size_condLt, size_var, size_add, size_lit]
          omega)
      (show J (σ.setVar i 0) from ⟨0, Nat.zero_le _, by simp, h0⟩)
  have hkN : k = N := by
    rw [evalB_condLt (evalB_var (by omega)) (he k hk σ' hI hik)] at hfalse
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega
  rw [hkN] at hI hik
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hrun).mono ?_, hI, hik⟩
  simp only [Φ, vars_setVar, if_true, hik, Ico_self, sum_empty, add_zero, ← range_eq_Ico] at hK
  simp only [size_condLt, size_var, size_lit] at hK ⊢
  omega

/-! ### The value bound -/

/-- The bound on values: `B` exceeds `8 (n + 2)^3`. -/
def WB (n B : ℕ) : Prop := (n + 2) ^ 3 * 8 < B

theorem WB.small {n B : ℕ} (h : WB n B) : n * n + 2 * n + 3 < B := by
  unfold WB at h; nlinarith

theorem WB.big {n B t : ℕ} (h : WB n B) (ht : t < n * n) :
    t * (2 * n + 2) + (2 * n + 2) + 2 < B := by
  unfold WB at h
  have : (t + 1) * (2 * n + 2) ≤ n * n * (2 * n + 2) := Nat.mul_le_mul_right _ ht
  nlinarith

theorem rm_lt {n u v : ℕ} (hu : u < n) (hv : v < n) : u * n + v < n * n := rowMajor_lt hu hv

/-! ### Crossing on numbers -/

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

variable (G) in
/-- `x` crosses the pair `u v`, on numbers. -/
def crN (x u v : ℕ) : Prop :=
  ∃ (hx : x < n) (hu : u < n) (hv : v < n), CrossesPair G ⟨x, hx⟩ ⟨u, hu⟩ ⟨v, hv⟩

instance (x u v : ℕ) : Decidable (crN G x u v) := by unfold crN; infer_instance

theorem crN_fin (x u v : Fin n) : crN G x u v ↔ CrossesPair G x u v :=
  ⟨fun ⟨_, _, _, h⟩ => h, fun h => ⟨x.2, u.2, v.2, h⟩⟩

theorem crN_lt {x u v : ℕ} (h : crN G x u v) : x < n ∧ u < n ∧ v < n := ⟨h.1, h.2.1, h.2.2.1⟩

theorem crN_iff {x u v : ℕ} (hx : x < n) (hu : u < n) (hv : v < n) :
    crN G x u v ↔ ¬ ((x = u ∨ gA G x u) ↔ (x = v ∨ gA G x v)) := by
  rw [gA_iff hx hu, gA_iff hx hv]
  constructor
  · rintro ⟨_, _, _, h⟩
    simpa [CrossesPair, Fin.ext_iff] using h
  · intro h
    exact ⟨hx, hu, hv, by simpa [CrossesPair, Fin.ext_iff] using h⟩

theorem crN_self (x u : ℕ) : ¬ crN G x u u := fun ⟨_, _, _, h⟩ => h Iff.rfl

/-- `1` if the vertex in `x` crosses the pair in `u` and `v`, else `0`. -/
def wCrossE (x u v : String) : Expr :=
  .xor (.or (eqE x u) (.get "adj" (rm x u))) (.or (eqE x v) (.get "adj" (rm x v)))

@[simp] theorem size_crossE (x u v : String) : (wCrossE x u v).size = 33 := rfl

theorem evalB_crossE {B : ℕ} {τ : Env} {xs us vs : String} {x u v : ℕ} (hn : τ.vars "n" = n)
    (hadj : Mat τ "adj" n (fun u v => ind (gA G u v))) (hx : τ.vars xs = x)
    (hu : τ.vars us = u) (hv : τ.vars vs = v) (hxn : x < n) (hun : u < n) (hvn : v < n)
    (hB : n * n + 2 < B) :
    (wCrossE xs us vs).evalB B τ = some (ind (crN G x u v)) := by
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have e1 := evalB_eqE (B := B) (σ := τ) (x := xs) (y := us) (by rw [hx]; omega)
    (by rw [hu]; omega) (by omega)
  have e2 := evalB_eqE (B := B) (σ := τ) (x := xs) (y := vs) (by rw [hx]; omega)
    (by rw [hv]; omega) (by omega)
  rw [hx, hu] at e1
  rw [hx, hv] at e2
  have a1 := hadj.evalB (B := B) hn hx hu hxn hun (by omega) (by omega)
    (by have := ind_le_one (gA G x u); omega)
  have a2 := hadj.evalB (B := B) hn hx hv hxn hvn (by omega) (by omega)
    (by have := ind_le_one (gA G x v); omega)
  have := evalB_xor01 (evalB_or01 e1 a1 (by omega)) (evalB_or01 e2 a2 (by omega)) (by omega)
  rw [wCrossE, this]
  congr 1
  exact ind_eq_iff.2 (crN_iff hxn hun hvn).symm

theorem evalB_condCross {B : ℕ} {τ : Env} {xs us vs : String} {x u v : ℕ}
    (hn : τ.vars "n" = n)
    (hadj : Mat τ "adj" n (fun u v => ind (gA G u v))) (hx : τ.vars xs = x)
    (hu : τ.vars us = u) (hv : τ.vars vs = v) (hxn : x < n) (hun : u < n) (hvn : v < n)
    (hB : n * n + 2 < B) :
    (Cond.eq (wCrossE xs us vs) (.lit 1)).evalB B τ = some (decide (crN G x u v)) := by
  rw [evalB_condEq' (evalB_crossE hn hadj hx hu hv hxn hun hvn hB) (evalB_lit (by omega))]
  simp [ind_eq_one]

/-! ### The values `ξ` as sums -/

variable (G) in
/-- The total weight `Σ_{x < k} [x crosses u v] 2 ^ c x`. -/
noncomputable def xiP (c : ℕ → ℕ) (k u v : ℕ) : ℕ := ∑ x ∈ range k, ind (crN G x u v) * 2 ^ c x

theorem xiP_succ (c : ℕ → ℕ) (k u v : ℕ) :
    xiP G c (k + 1) u v = xiP G c k u v + ind (crN G k u v) * 2 ^ c k := by
  unfold xiP; rw [sum_range_succ]

theorem xiP_zero (c : ℕ → ℕ) (u v : ℕ) : xiP G c 0 u v = 0 := by simp [xiP]

theorem xiP_congr {c c' : ℕ → ℕ} {k : ℕ} (h : ∀ x < k, c x = c' x) (u v : ℕ) :
    xiP G c k u v = xiP G c' k u v :=
  sum_congr rfl fun x hx => by rw [h x (mem_range.1 hx)]

theorem xiP_le {c : ℕ → ℕ} {k K : ℕ} (h : ∀ x < k, c x ≤ K) (u v : ℕ) :
    xiP G c k u v ≤ k * 2 ^ K := by
  unfold xiP
  have : ∀ x ∈ range k, ind (crN G x u v) * 2 ^ c x ≤ 2 ^ K := fun x hx => by
    have h1 := ind_le_one (crN G x u v)
    have h2 : 2 ^ c x ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (h x (mem_range.1 hx))
    exact (Nat.mul_le_mul_right _ h1).trans (by simpa using h2)
  have := sum_le_card_nsmul (range k) _ _ this
  simpa using this

/-- Doubling the weight of `k` when it satisfies `q`. -/
theorem xiP_double (c : ℕ → ℕ) (q : ℕ → Prop) {k N : ℕ} (hk : k < N) (u v : ℕ) :
    xiP G (fun x => c x + ind (x < k + 1 ∧ q x)) N u v =
      xiP G (fun x => c x + ind (x < k ∧ q x)) N u v + ind (crN G k u v ∧ q k) * 2 ^ c k := by
  unfold xiP
  have hx : ∀ x ∈ range N, ind (crN G x u v) * 2 ^ (c x + ind (x < k + 1 ∧ q x)) =
      ind (crN G x u v) * 2 ^ (c x + ind (x < k ∧ q x)) +
        if k = x then ind (crN G k u v ∧ q k) * 2 ^ c k else 0 := by
    intro x _
    by_cases hkx : k = x
    · subst hkx
      simp only [if_true]
      unfold ind
      by_cases hc : crN G k u v <;> by_cases hq : q k <;> simp [hc, hq, pow_succ]
      all_goals omega
    · have : (x < k + 1 ∧ q x) ↔ (x < k ∧ q x) := by
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      simp only [hkx, if_false, add_zero]
      rw [ind_eq_iff.2 this]
  rw [sum_congr rfl hx, sum_add_distrib, sum_ite_eq]
  simp [mem_range.2 hk]

theorem log_le_of_le {x K : ℕ} (h : x ≤ n * 2 ^ K) : Nat.log 2 x ≤ K + Nat.log 2 n := by
  rcases Nat.eq_zero_or_pos x with h0 | hpos
  · simp [h0]
  have hn : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have : x < 2 ^ (K + Nat.log 2 n + 1) := by
    calc x ≤ n * 2 ^ K := h
      _ < 2 ^ (Nat.log 2 n + 1) * 2 ^ K := by
          apply Nat.mul_lt_mul_of_pos_right hn (by positivity)
      _ = 2 ^ (K + Nat.log 2 n + 1) := by rw [← pow_add]; ring_nf
  have := Nat.log_lt_of_lt_pow (by omega) this
  omega

/-! ### All values -/

/-- The numbers `u * n + v` for `u, v < n` represent `F u v`. -/
def XiRep (n : ℕ) (F : ℕ → ℕ → ℕ) (τ : Env) : Prop :=
  ∀ u < n, ∀ v < n, BigRep (2 * n + 2) τ (u * n + v) (F u v)

theorem BigRep.of_arrs {D t x : ℕ} {σ τ : Env} (h : BigRep D σ t x) (he : τ.arrs = σ.arrs) :
    BigRep D τ t x := by
  have hb : bigBits D τ = bigBits D σ := by funext s i; simp [bigBits, he]
  have ht : bigTop τ = bigTop σ := by funext s; simp [bigTop, he]
  exact ⟨by rw [he]; exact h.lenb, by rw [he]; exact h.lent, by rw [hb]; exact h.bit_le,
    by rw [hb]; exact h.val, by rw [ht]; exact h.top_le, by rw [hb, ht]; exact h.zero,
    by rw [hb, ht]; exact h.top_bit⟩

theorem XiRep.of_arrs {F : ℕ → ℕ → ℕ} {σ τ : Env} (h : XiRep n F σ)
    (hx : τ.arrs "xb" = σ.arrs "xb") (ht : τ.arrs "xt" = σ.arrs "xt") : XiRep n F τ := by
  intro u hu v hv
  have h0 := h u hu v hv
  have hb : bigBits (2 * n + 2) τ = bigBits (2 * n + 2) σ := by funext s i; simp [bigBits, hx]
  have ht' : bigTop τ = bigTop σ := by funext s; simp [bigTop, ht]
  exact ⟨by rw [hx]; exact h0.lenb, by rw [ht]; exact h0.lent, by rw [hb]; exact h0.bit_le,
    by rw [hb]; exact h0.val, by rw [ht']; exact h0.top_le, by rw [hb, ht']; exact h0.zero,
    by rw [hb, ht']; exact h0.top_bit⟩

theorem XiRep.congr {F F' : ℕ → ℕ → ℕ} {τ : Env} (h : XiRep n F τ)
    (hF : ∀ u < n, ∀ v < n, F u v = F' u v) : XiRep n F' τ :=
  fun u hu v hv => by rw [← hF u hu v hv]; exact h u hu v hv

theorem XiRep.mk' {F F' : ℕ → ℕ → ℕ} {σ τ : Env} (h : XiRep n F σ)
    (hx : τ.arrs "xb" = σ.arrs "xb") (ht : τ.arrs "xt" = σ.arrs "xt")
    (hF : ∀ u < n, ∀ v < n, F u v = F' u v) : XiRep n F' τ :=
  (h.of_arrs hx ht).congr hF

theorem ind_split {P Q R : Prop} (c : ℕ) (h : R ↔ P ∨ Q) (hn : ¬ (P ∧ Q)) :
    ind P * c + ind Q * c = ind R * c := by
  unfold ind; by_cases hp : P <;> by_cases hq : Q <;> simp_all

/-- **Adding a power of two to one value.** -/
theorem addPow_at {B a b j : ℕ} {F : ℕ → ℕ → ℕ} {τ : Env} (hB : WB n B) (hrep : XiRep n F τ)
    (ha : a < n) (hb : b < n) (ht : τ.vars "bt" = a * n + b) (hj : τ.vars "bj" = j)
    (hD : τ.vars "D" = 2 * n + 2) (hjD : j < 2 * n + 2) (hval : F a b + 2 ^ j < 2 ^ (2 * n + 2)) :
    ∃ τ' K, Run B addPow τ τ' K ∧
      XiRep n (fun u v => F u v + ind (u = a ∧ v = b) * 2 ^ j) τ' ∧
      Fr ["bk"] ["xb", "xt"] τ τ' ∧ K ≤ 20 * Nat.log 2 (F a b + 2 ^ j) + 30 := by
  have htn := rm_lt ha hb
  obtain ⟨τ', K, hr, hR, hF, hv, hK⟩ := addPow_run (B := B) (hrep a ha b hb) ht hj hD hjD hval
    (hB.big htn)
  refine ⟨τ', K, hr, fun u hu v hv' => ?_, ⟨fun y hy => hv y (by simpa using hy),
    fun c hc => hF.arrs c (by simp at hc; exact hc.1) (by simp at hc; exact hc.2), hF.inp, hF.out⟩,
    hK⟩
  by_cases he : u = a ∧ v = b
  · obtain ⟨rfl, rfl⟩ := he
    simpa [ind] using hR
  · have hne : u * n + v ≠ a * n + b := fun e => he (rowMajor_inj hv' hb e)
    have : ind (u = a ∧ v = b) = 0 := by simp [ind, he]
    simp only [this, zero_mul, add_zero]
    exact (hrep u hu v hv').frame hF hne

/-! ### The update for one vertex -/

/-- The static part of the environment. -/
structure WCtx (n : ℕ) (G : SimpleGraph (Fin n)) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hD : τ.vars "D" = 2 * n + 2
  hadj : Mat τ "adj" n (fun u v => ind (gA G u v))

theorem WCtx.fr {W Wa : List String} {σ τ : Env} (h : WCtx n G σ) (F : Fr W Wa σ τ)
    (h1 : "n" ∉ W) (h2 : "D" ∉ W) (h3 : "adj" ∉ Wa) : WCtx n G τ :=
  ⟨by rw [F.vars _ h1, h.hn], by rw [F.vars _ h2, h.hD], h.hadj.of_eq (F.arrs _ h3)⟩

/-- Add the weight of `wx` to the value of the pair `wa wb` if `wx`
crosses it. -/
def updBody : Com :=
  .ite (.eq (wCrossE "wx" "wa" "wb") (.lit 1))
    (.seq (.assign "bt" (rm "wa" "wb")) (.seq (.assign "bj" (.get "wc" (.var "wx"))) addPow)) .skip

/-- Add the weight of `wx` to the values of all pairs it crosses. -/
def updX : Com := forUp "wa" (.var "n") (forUp "wb" (.var "n") updBody)

/-- The cost of `updX` when every addition costs at most `P`. -/
def uxC (n P : ℕ) : ℕ := n * (n * (P + 53) + 14) + 6

theorem updBody_run {B x a b j P : ℕ} {F : ℕ → ℕ → ℕ} {τ : Env} (hB : WB n B)
    (hC : WCtx n G τ) (hx : τ.vars "wx" = x) (ha : τ.vars "wa" = a) (hb : τ.vars "wb" = b)
    (hxn : x < n) (han : a < n) (hbn : b < n)
    (hwc : (τ.arrs "wc")[x]? = some j) (hjD : j < 2 * n + 2) (hrep : XiRep n F τ)
    (hval : crN G x a b → F a b + 2 ^ j < 2 ^ (2 * n + 2))
    (hP : crN G x a b → 20 * Nat.log 2 (F a b + 2 ^ j) + 30 ≤ P) :
    ∃ τ', Run B updBody τ τ' (P + 45) ∧
      XiRep n (fun u v => F u v + ind (u = a ∧ v = b ∧ crN G x a b) * 2 ^ j) τ' ∧
      Fr ["bt", "bj", "bk"] ["xb", "xt"] τ τ' := by
  have hs := hB.small
  have hcond := evalB_condCross (B := B) hC.hn hC.hadj hx ha hb hxn han hbn (by omega)
  have htn := rm_lt han hbn
  by_cases hcr : crN G x a b
  · have hr1 := Run.assign (B := B) (σ := τ) (x := "bt") (e := rm "wa" "wb") (v := a * n + b)
      (evalB_rm ha hC.hn hb hbn (by omega) (by omega))
    have hr2 := Run.assign (B := B) (σ := τ.setVar "bt" (a * n + b)) (x := "bj")
      (e := .get "wc" (.var "wx")) (v := j)
      (evalB_getVar (i := x) (by simp [hx]) (by omega) (by simpa using hwc) (by omega))
    obtain ⟨τ', K, hr3, hR, hF, hK⟩ := addPow_at (B := B) (τ := (τ.setVar "bt" (a * n + b)).setVar
      "bj" j) (F := F) (j := j) hB (hrep.of_arrs rfl rfl) han hbn (by simp) (by simp)
      (by simp [hC.hD]) hjD (hval hcr)
    refine ⟨τ', (Run.ite_true (by rw [hcond]; simp [hcr]) (Run.seq hr1 (Run.seq hr2 hr3))).mono
      (by have := hP hcr; simp; omega), hR.congr fun u _ v _ => by simp [hcr], ?_⟩
    exact ((((Fr.refl _ _ τ).setVar (by simp) _).setVar (by simp) _).trans
      (hF.mono (by simp) (by simp)))
  · refine ⟨τ, (Run.ite_false (by rw [hcond]; simp [hcr]) Run.skip).mono (by simp),
      hrep.congr fun u _ v _ => by simp [hcr, ind], Fr.refl _ _ τ⟩

/-- **The update for one vertex.** If `wx` holds `x` and `wc[x] = j`, the
command `updX` adds `2 ^ j` to the value of every pair crossed by `x`. -/
theorem updX_run {B x j P : ℕ} {F : ℕ → ℕ → ℕ} {σ : Env} (hB : WB n B)
    (hC : WCtx n G σ) (hx : σ.vars "wx" = x) (hxn : x < n)
    (hwc : (σ.arrs "wc")[x]? = some j) (hjD : j < 2 * n + 2) (hrep : XiRep n F σ)
    (hval : ∀ u < n, ∀ v < n, crN G x u v → F u v + 2 ^ j < 2 ^ (2 * n + 2))
    (hP : ∀ u < n, ∀ v < n, crN G x u v → 20 * Nat.log 2 (F u v + 2 ^ j) + 30 ≤ P) :
    ∃ σ', Run B updX σ σ' (uxC n P) ∧
      XiRep n (fun u v => F u v + ind (crN G x u v) * 2 ^ j) σ' ∧
      Fr ["wa", "wb", "bt", "bj", "bk"] ["xb", "xt"] σ σ' := by
  have hs := hB.small
  let W : List String := ["wa", "wb", "bt", "bj", "bk"]
  let Wa : List String := ["xb", "xt"]
  let I : ℕ → Env → Prop := fun a τ => Fr W Wa σ τ ∧
    XiRep n (fun u v => F u v + ind (u < a ∧ crN G x u v) * 2 ^ j) τ
  have hCτ : ∀ τ, Fr W Wa σ τ → WCtx n G τ := fun τ hF => hC.fr hF (by decide) (by decide)
    (by decide)
  obtain ⟨σ', hr, ⟨hF', hR'⟩, -⟩ :=
    forUp_run (B := B) (i := "wa") (e := .var "n") (body := forUp "wb" (.var "n") updBody)
      (N := n) (K := n * (P + 53) + 6) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hCτ τ hI.1).hn]; omega), (hCτ τ hI.1).hn])
      (σ := σ) ⟨(Fr.refl W Wa σ).setVar (by simp [W]) 0, XiRep.mk' hrep rfl rfl
        fun u _ v _ => by simp [ind]⟩
      (by
        rintro a ha τ ⟨hFτ, hRτ⟩ hwa
        let J : ℕ → Env → Prop := fun b ρ => Fr W Wa σ ρ ∧ ρ.vars "wa" = a ∧
          XiRep n (fun u v => F u v + ind ((u < a ∨ (u = a ∧ v < b)) ∧ crN G x u v) * 2 ^ j) ρ
        obtain ⟨ρ, hrI, ⟨hFρ, haρ, hRρ⟩, -⟩ :=
          forUp_run (B := B) (i := "wb") (e := .var "n") (body := updBody) (N := n)
            (K := P + 45) J (by omega)
            (fun k _ ρ hI _ => by
              rw [evalB_var (by rw [(hCτ ρ hI.1).hn]; omega), (hCτ ρ hI.1).hn])
            (σ := τ) ⟨hFτ.setVar (by simp [W]) 0, by simp [hwa], XiRep.mk' hRτ rfl rfl
              fun u _ v _ => by
                congr 3
                apply propext
                constructor
                · rintro ⟨h1, h2⟩; exact ⟨Or.inl h1, h2⟩
                · rintro ⟨h1 | ⟨_, h1⟩, h2⟩
                  · exact ⟨h1, h2⟩
                  · omega⟩
            (by
              rintro b hb ρ ⟨hFρ, haρ, hRρ⟩ hwb
              have hCρ := hCτ ρ hFρ
              have hxρ : ρ.vars "wx" = x := by rw [hFρ.vars _ (by decide), hx]
              have hwcρ : (ρ.arrs "wc")[x]? = some j := by rw [hFρ.arrs _ (by decide), hwc]
              obtain ⟨ρ', hr', hR', hF'⟩ := updBody_run (B := B) (P := P) hB hCρ hxρ haρ hwb hxn ha
                hb hwcρ hjD hRρ
                (by intro hc; have := hval a ha b hb hc; simpa [ind] using this)
                (by intro hc; have := hP a ha b hb hc; simpa [ind] using this)
              refine ⟨ρ', hr', by rw [hF'.vars _ (by decide), hwb], ?_, ?_, ?_⟩
              · exact (hFρ.trans (hF'.mono (by simp [W]) (by simp [Wa]))).setVar (by simp [W]) _
              · simp [hF'.vars _ (by decide : "wa" ∉ ["bt", "bj", "bk"]), haρ]
              · refine XiRep.mk' hR' rfl rfl fun u hu v hv => ?_
                rw [add_assoc, ind_split]
                · constructor
                  · rintro ⟨h | ⟨rfl, h⟩, hc⟩
                    · exact Or.inl ⟨Or.inl h, hc⟩
                    · rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
                      · exact Or.inl ⟨Or.inr ⟨rfl, h⟩, hc⟩
                      · exact Or.inr ⟨rfl, rfl, hc⟩
                  · rintro (⟨h, hc⟩ | ⟨rfl, rfl, hc⟩)
                    · refine ⟨?_, hc⟩
                      rcases h with h | ⟨h1, h2⟩
                      · exact Or.inl h
                      · exact Or.inr ⟨h1, by omega⟩
                    · exact ⟨Or.inr ⟨rfl, by omega⟩, hc⟩
                · rintro ⟨⟨h | ⟨_, h⟩, _⟩, rfl, rfl, _⟩ <;> omega)
        refine ⟨ρ, hrI.mono (by simp), haρ, hFρ.setVar (by simp [W]) _, ?_⟩
        refine XiRep.mk' hRρ rfl rfl fun u hu v hv => ?_
        congr 3
        apply propext
        constructor
        · rintro ⟨h1 | ⟨h1, _⟩, h2⟩
          · exact ⟨by omega, h2⟩
          · exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | h1
          · exact ⟨Or.inl h1, h2⟩
          · exact ⟨Or.inr ⟨h1, hv⟩, h2⟩)
  refine ⟨σ', hr.mono (by simp [uxC]), hR'.congr fun u hu v _ => by simp [hu], hF'⟩

end Lax185574Proofs.Chain.Ram
