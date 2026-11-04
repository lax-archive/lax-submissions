import Lax185574Proofs.Chain.Ram.Bool01

/-!
Binary big numbers stored in one array.

The number with index `t` has its bits in the array `xb` at the positions
`t * D + k` for `k < D`, where the scalar `D` holds `D`, and its length in
the array `xt` at position `t` (`BigRep`). The length is exact: it is `0`
for the number `0`, and otherwise the highest bit set is the one below the
length. So the length is `Nat.log 2 x + 1` for `x > 0` (`BigRep.top_le_log`).

Two commands work on such numbers.

* `addPow` adds `2 ^ j` to the number with index `t`, where `t` is in the
  scalar `bt` and `j` in the scalar `bj`. It runs the carry from bit `j`
  upwards in the scratch scalar `bk` and then updates the length. Its cost
  is linear in the length of the result (`addPow_run`).
* `bigCmp` compares the numbers with indices in the scalars `ca1` and
  `ca2` and leaves `1` in `blt` if the first is smaller, else `0`. It
  compares the lengths and, if they agree, scans the bits from the top
  down in the scratch scalar `bk` (`bigCmp_run`).

Both commands touch nothing but the scalars named above, and `addPow`
writes only the bits and the length of its own number (`BigFrame`), so the
representations of all other numbers survive (`BigRep.frame`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574Proofs.Conversions.Ram

/-! ### Values of bit sequences -/

/-- The value of the bits `b 0, …, b (k - 1)`. -/
def bval (b : ℕ → ℕ) (k : ℕ) : ℕ := ∑ i ∈ range k, b i * 2 ^ i

@[simp] theorem bval_zero (b : ℕ → ℕ) : bval b 0 = 0 := by simp [bval]

theorem bval_succ (b : ℕ → ℕ) (k : ℕ) : bval b (k + 1) = bval b k + b k * 2 ^ k := by
  simp [bval, sum_range_succ]

theorem bval_lt_two_pow {b : ℕ → ℕ} {n : ℕ} (h : ∀ k < n, b k ≤ 1) : bval b n < 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [bval_succ, pow_succ]
    have h1 := ih (fun k hk => h k (by omega))
    have h2 : b n * 2 ^ n ≤ 1 * 2 ^ n := Nat.mul_le_mul_right _ (h n (by omega))
    omega

theorem bval_congr {b c : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, b i = c i) : bval b n = bval c n :=
  sum_congr rfl fun i hi => by rw [h i (mem_range.1 hi)]

theorem single_le_bval {b : ℕ → ℕ} {n i : ℕ} (hi : i < n) : b i * 2 ^ i ≤ bval b n :=
  single_le_sum (f := fun i => b i * 2 ^ i) (fun j _ => Nat.zero_le _) (mem_range.2 hi)

theorem bval_eq_of_zero {b : ℕ → ℕ} {T D : ℕ} (hT : T ≤ D)
    (hz : ∀ k, T ≤ k → k < D → b k = 0) : bval b D = bval b T := by
  induction D, hT using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [bval_succ, hz n hn (by omega), zero_mul, add_zero]
    exact ih fun k h1 h2 => hz k h1 (by omega)

/-- Changing bit `k` to `v`. -/
theorem bval_update {b : ℕ → ℕ} {n k : ℕ} (v : ℕ) (hk : k < n) :
    bval (fun i => if i = k then v else b i) n + b k * 2 ^ k = bval b n + v * 2 ^ k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [bval_succ, bval_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · have := ih h
      rw [if_neg (show n ≠ k by omega)]
      omega
    · subst h
      rw [if_pos rfl, bval_congr (c := b) (fun i hi => if_neg (by omega))]
      ring

/-- Two bit sequences that agree above position `i` and have `0` and `1`
at `i` are ordered. -/
theorem bval_lt_of_diff {b c : ℕ → ℕ} {D i : ℕ} (hb : ∀ k < D, b k ≤ 1) (hiD : i < D)
    (hbi : b i = 0) (hci : c i = 1) (hag : ∀ k, i < k → k < D → b k = c k) :
    bval b D < bval c D := by
  have key : ∀ n, i + 1 ≤ n → n ≤ D → bval b n < bval c n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro _
      rw [bval_succ, bval_succ, hbi, hci, zero_mul, one_mul, add_zero]
      have := bval_lt_two_pow (b := b) (n := i) (fun k hk => hb k (by omega))
      omega
    | succ n hn ih =>
      intro hnD
      rw [bval_succ, bval_succ, hag n (by omega) (by omega)]
      have := ih (by omega)
      omega
  exact key D (by omega) le_rfl

/-- **Comparison by the highest differing bit.** -/
theorem ind_lt_of_diff {b c : ℕ → ℕ} {D i : ℕ} (hb : ∀ k < D, b k ≤ 1)
    (hc : ∀ k < D, c k ≤ 1) (hiD : i < D) (hne : b i ≠ c i)
    (hag : ∀ k, i < k → k < D → b k = c k) : ind (bval b D < bval c D) = c i := by
  have h1 := hb i hiD
  have h2 := hc i hiD
  rcases (show (c i = 1 ∧ b i = 0) ∨ (c i = 0 ∧ b i = 1) by omega) with ⟨hc1, hb0⟩ | ⟨hc0, hb1⟩
  · rw [hc1]; exact ind_eq_one.2 (bval_lt_of_diff hb hiD hb0 hc1 hag)
  · rw [hc0]
    have := bval_lt_of_diff hc hiD hc0 hb1 (fun k h1 h2 => (hag k h1 h2).symm)
    unfold ind; rw [if_neg (by omega)]

/-- A sequence that is zero from `T` on is smaller than one with a bit
set at `U - 1 ≥ T`. -/
theorem bval_lt_of_top_lt {b c : ℕ → ℕ} {D T U : ℕ} (hb : ∀ k < D, b k ≤ 1) (hT : T ≤ D)
    (hz : ∀ k, T ≤ k → k < D → b k = 0) (hU : U ≤ D) (hcU : c (U - 1) = 1) (hTU : T < U) :
    bval b D < bval c D := by
  rw [bval_eq_of_zero hT hz]
  have h1 := bval_lt_two_pow (b := b) (n := T) (fun k hk => hb k (by omega))
  have h2 := single_le_bval (b := c) (n := D) (i := U - 1) (by omega)
  rw [hcU, one_mul] at h2
  have h3 : 2 ^ T ≤ 2 ^ (U - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ### Lists -/

theorem getElem?_eq_some_getD {l : List ℕ} {p : ℕ} (h : p < l.length) :
    l[p]? = some (l.getD p 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem getD_set_self {l : List ℕ} {p v : ℕ} (h : p < l.length) : (l.set p v).getD p 0 = v := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_set_ne {l : List ℕ} {p q v : ℕ} (h : q ≠ p) :
    (l.set p v).getD q 0 = l.getD q 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm h)]

theorem getD_congr {l l' : List ℕ} {p : ℕ} (h : l'[p]? = l[p]?) : l'.getD p 0 = l.getD p 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, h]

/-! ### The representation -/

/-- Bit `i` of the number with index `t`. -/
def bigBits (D : ℕ) (τ : Env) (t i : ℕ) : ℕ := (τ.arrs "xb").getD (t * D + i) 0

/-- The length of the number with index `t`. -/
def bigTop (τ : Env) (t : ℕ) : ℕ := (τ.arrs "xt").getD t 0

@[simp] theorem bigBits_setVar (D : ℕ) (τ : Env) (y : String) (v t : ℕ) :
    bigBits D (τ.setVar y v) t = bigBits D τ t := rfl

@[simp] theorem bigTop_setVar (τ : Env) (y : String) (v t : ℕ) :
    bigTop (τ.setVar y v) t = bigTop τ t := rfl

/-- The number with index `t` is `x`: the bits are `0` or `1` and have
value `x`, and the length is exact. -/
structure BigRep (D : ℕ) (τ : Env) (t x : ℕ) : Prop where
  lenb : t * D + D ≤ (τ.arrs "xb").length
  lent : t < (τ.arrs "xt").length
  bit_le : ∀ k < D, bigBits D τ t k ≤ 1
  val : bval (bigBits D τ t) D = x
  top_le : bigTop τ t ≤ D
  zero : ∀ k, bigTop τ t ≤ k → k < D → bigBits D τ t k = 0
  top_bit : 0 < bigTop τ t → bigBits D τ t (bigTop τ t - 1) = 1

/-- The length is at most `Nat.log 2 x + 1`. -/
theorem BigRep.top_le_log {D t x : ℕ} {τ : Env} (h : BigRep D τ t x) :
    bigTop τ t ≤ Nat.log 2 x + 1 := by
  rcases Nat.eq_zero_or_pos (bigTop τ t) with h0 | hpos
  · omega
  · have h1 := single_le_bval (b := bigBits D τ t) (n := D) (i := bigTop τ t - 1)
      (by have := h.top_le; omega)
    rw [h.top_bit hpos, one_mul, h.val] at h1
    have := Nat.le_log_of_pow_le (by norm_num) h1
    omega

/-- A shorter number is smaller. -/
theorem BigRep.lt_of_top_lt {D t t' x x' : ℕ} {τ τ' : Env} (h : BigRep D τ t x)
    (h' : BigRep D τ' t' x') (hlt : bigTop τ t < bigTop τ' t') : x < x' := by
  rw [← h.val, ← h'.val]
  exact bval_lt_of_top_lt h.bit_le h.top_le h.zero h'.top_le (h'.top_bit (by omega)) hlt

/-- **The number zero.** All bits and the length zero represent `0`. -/
theorem bigRep_zero {D t : ℕ} {τ : Env} (hlb : t * D + D ≤ (τ.arrs "xb").length)
    (hlt : t < (τ.arrs "xt").length) (hb : ∀ k < D, (τ.arrs "xb")[t * D + k]? = some 0)
    (ht : (τ.arrs "xt")[t]? = some 0) : BigRep D τ t 0 := by
  have hb' : ∀ k < D, bigBits D τ t k = 0 := fun k hk => by
    simp [bigBits, List.getD_eq_getElem?_getD, hb k hk]
  have ht' : bigTop τ t = 0 := by simp [bigTop, List.getD_eq_getElem?_getD, ht]
  refine ⟨hlb, hlt, fun k hk => by rw [hb' k hk]; omega, ?_, by omega,
    fun k _ hk => hb' k hk, fun h => by omega⟩
  rw [bval_congr (c := fun _ => 0) hb']
  simp [bval]

/-- What a command on the number `t` may change: the bits and the length
of `t`, nothing else of the arrays and nothing of the tapes. -/
structure BigFrame (D t : ℕ) (σ τ : Env) : Prop where
  arrs : ∀ a, a ≠ "xb" → a ≠ "xt" → τ.arrs a = σ.arrs a
  lenb : (τ.arrs "xb").length = (σ.arrs "xb").length
  lent : (τ.arrs "xt").length = (σ.arrs "xt").length
  xb : ∀ p, (p < t * D ∨ t * D + D ≤ p) → (τ.arrs "xb")[p]? = (σ.arrs "xb")[p]?
  xt : ∀ p, p ≠ t → (τ.arrs "xt")[p]? = (σ.arrs "xt")[p]?
  inp : τ.inp = σ.inp
  out : τ.out = σ.out

/-- **Other numbers survive.** -/
theorem BigRep.frame {D t t' x : ℕ} {σ τ : Env} (h : BigRep D σ t' x) (F : BigFrame D t σ τ)
    (hne : t' ≠ t) : BigRep D τ t' x := by
  have hbits : ∀ k < D, bigBits D τ t' k = bigBits D σ t' k := fun k hk => by
    unfold bigBits
    refine getD_congr (F.xb _ ?_)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · left
      have := Nat.mul_le_mul_right D (show t' + 1 ≤ t by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
    · right
      have := Nat.mul_le_mul_right D (show t + 1 ≤ t' by omega)
      rw [Nat.add_mul, one_mul] at this
      omega
  have htop : bigTop τ t' = bigTop σ t' := getD_congr (F.xt _ hne)
  refine ⟨by rw [F.lenb]; exact h.lenb, by rw [F.lent]; exact h.lent,
    fun k hk => by rw [hbits k hk]; exact h.bit_le k hk, by rw [bval_congr hbits, h.val],
    by rw [htop]; exact h.top_le,
    fun k hk hkD => by rw [hbits k hkD]; exact h.zero k (by omega) hkD,
    fun hp => ?_⟩
  rw [htop] at hp ⊢
  rw [hbits _ (by have := h.top_le; omega)]
  exact h.top_bit hp

theorem bigBits_of_set {D t k v : ℕ} {ρ τ : Env}
    (h : ρ.arrs "xb" = (τ.arrs "xb").set (t * D + k) v)
    (hlen : t * D + k < (τ.arrs "xb").length) :
    bigBits D ρ t = fun i => if i = k then v else bigBits D τ t i := by
  funext i
  unfold bigBits
  rw [h]
  split
  · subst_vars; exact getD_set_self hlen
  · exact getD_set_ne (by omega)

/-! ### Positions of bits -/

/-- The position `a · D + bk` of the bit array. -/
def ixE (a : String) : Expr := .add (.mul (.var a) (.var "D")) (.var "bk")

@[simp] theorem size_ixE (a : String) : (ixE a).size = 5 := rfl

theorem evalB_ixE {B : ℕ} {τ : Env} {a : String} {t D k : ℕ} (ha : τ.vars a = t)
    (hD : τ.vars "D" = D) (hk : τ.vars "bk" = k) (htB : t < B) (hDB : D < B)
    (h : t * D + k < B) : (ixE a).evalB B τ = some (t * D + k) := by
  have := evalB_bin (op := .add) (evalB_bin (op := .mul) (evalB_var (B := B) (x := a) (σ := τ)
    (by omega)) (evalB_var (x := "D") (by omega)) (by simp [ha, hD]; omega))
    (evalB_var (x := "bk") (by omega)) (by simp [ha, hD, hk]; omega)
  simpa [ixE, ha, hD, hk] using this

/-! ### Adding a power of two -/

/-- The carry loop: clear the bits from `bk` upwards while they are set. -/
def addPowLoop : Com :=
  .while (.eq (.get "xb" (ixE "bt")) (.lit 1))
    (.seq (.store "xb" (ixE "bt") (.lit 0)) (.assign "bk" (.add (.var "bk") (.lit 1))))

/-- Set bit `bk` and raise the length to `bk + 1` if it is smaller. -/
def addPowEnd : Com :=
  .seq (.store "xb" (ixE "bt") (.lit 1))
    (.ite (.lt (.get "xt" (.var "bt")) (.add (.var "bk") (.lit 1)))
      (.store "xt" (.var "bt") (.add (.var "bk") (.lit 1))) .skip)

/-- Add `2 ^ bj` to the number with index `bt`. -/
def addPow : Com := .seq (.assign "bk" (.var "bj")) (.seq addPowLoop addPowEnd)

/-- The invariant of the carry loop started from `σ`: the bits from `j`
to `bk - 1` were cleared, and adding `2 ^ bk` gives `x + 2 ^ j`. -/
structure CarryInv (D t j x : ℕ) (σ τ : Env) : Prop where
  hv : ∀ y, y ≠ "bk" → τ.vars y = σ.vars y
  ha : ∀ a, a ≠ "xb" → τ.arrs a = σ.arrs a
  hi : τ.inp = σ.inp
  ho : τ.out = σ.out
  hlen : (τ.arrs "xb").length = (σ.arrs "xb").length
  hout : ∀ p, (p < t * D + j ∨ t * D + τ.vars "bk" ≤ p) → (τ.arrs "xb")[p]? = (σ.arrs "xb")[p]?
  hjk : j ≤ τ.vars "bk"
  hbit : ∀ i < D, bigBits D τ t i ≤ 1
  hsum : x + 2 ^ j = bval (bigBits D τ t) D + 2 ^ τ.vars "bk"

theorem CarryInv.k_lt {D t j x : ℕ} {σ τ : Env} (h : CarryInv D t j x σ τ)
    (hx : x + 2 ^ j < 2 ^ D) : τ.vars "bk" < D := by
  by_contra hc
  have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show D ≤ τ.vars "bk" by omega)
  have := h.hsum
  omega

theorem CarryInv.pow_le {D t j x : ℕ} {σ τ : Env} (h : CarryInv D t j x σ τ) :
    2 ^ τ.vars "bk" ≤ x + 2 ^ j := by
  have := h.hsum; omega

/-- The bit at the carry position, read by the loop. -/
theorem CarryInv.evalB_bit {B D t j x : ℕ} {σ τ : Env} (h : CarryInv D t j x σ τ)
    (hrep : BigRep D σ t x) (hx : x + 2 ^ j < 2 ^ D) (hB : t * D + D + 2 < B)
    (ht : σ.vars "bt" = t) (hD : σ.vars "D" = D) :
    (ixE "bt").evalB B τ = some (t * D + τ.vars "bk") ∧
    t * D + τ.vars "bk" < (τ.arrs "xb").length ∧
    (Expr.get "xb" (ixE "bt")).evalB B τ = some (bigBits D τ t (τ.vars "bk")) := by
  have hkD := h.k_lt hx
  have htD : t ≤ t * D := Nat.le_mul_of_pos_right t (by omega)
  have hix := evalB_ixE (B := B) (τ := τ) (a := "bt") (k := τ.vars "bk")
    (by rw [h.hv _ (by decide), ht]) (by rw [h.hv _ (by decide), hD]) rfl (by omega) (by omega)
    (by omega)
  have hlen : t * D + τ.vars "bk" < (τ.arrs "xb").length := by
    rw [h.hlen]; have := hrep.lenb; omega
  exact ⟨hix, hlen, evalB_get hix (getElem?_eq_some_getD hlen)
    (by have := h.hbit _ hkD; omega)⟩

/-- **The carry loop.** -/
theorem addPowLoop_run {B D t j x : ℕ} {σ : Env} (hrep : BigRep D σ t x)
    (hx : x + 2 ^ j < 2 ^ D) (hB : t * D + D + 2 < B) (ht : σ.vars "bt" = t)
    (hD : σ.vars "D" = D) {τ0 : Env} (h0 : CarryInv D t j x σ τ0) :
    ∃ τ K, Run B addPowLoop τ0 τ K ∧ CarryInv D t j x σ τ ∧
      bigBits D τ t (τ.vars "bk") = 0 ∧
      K + 20 * (D - τ.vars "bk") ≤ 20 * (D - τ0.vars "bk") + 9 := by
  obtain ⟨τ, K, hr, hJ, hf, hK⟩ :=
    Run.while_potential (B := B) (b := .eq (.get "xb" (ixE "bt")) (.lit 1))
      (c := .seq (.store "xb" (ixE "bt") (.lit 0)) (.assign "bk" (.add (.var "bk") (.lit 1))))
      (CarryInv D t j x σ) (fun τ => 20 * (D - τ.vars "bk"))
      (fun τ hJ => ⟨_, evalB_condEq (hJ.evalB_bit hrep hx hB ht hD).2.2 (evalB_lit (by omega))⟩)
      (by
        intro τ hJ hc
        obtain ⟨hix, hlen, hget⟩ := hJ.evalB_bit hrep hx hB ht hD
        have hkD := hJ.k_lt hx
        obtain ⟨k, hk⟩ : ∃ k, τ.vars "bk" = k := ⟨_, rfl⟩
        rw [hk] at hix hlen hget hkD
        have hbit : bigBits D τ t k = 1 := by
          rw [evalB_condEq hget (evalB_lit (by omega))] at hc; simpa using hc
        have hbits := bigBits_of_set (D := D) (t := t) (k := k) (v := 0)
          (ρ := τ.setArr "xb" (t * D + k) 0) (τ := τ) (by simp) hlen
        refine ⟨(τ.setArr "xb" (t * D + k) 0).setVar "bk" (k + 1), _,
          Run.seq (Run.store (a := "xb") (i := ixE "bt") (e := .lit 0) (idx := t * D + k) (v := 0)
            hix (evalB_lit (by omega)) hlen)
            (Run.assign (x := "bk") (e := .add (.var "bk") (.lit 1)) (v := k + 1)
              (by simp [hk]; omega)), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · intro y hy; simp [hy, hJ.hv y hy]
        · intro a ha; simp [ha, hJ.ha a ha]
        · simp [hJ.hi]
        · simp [hJ.ho]
        · simp [hJ.hlen]
        · intro p hp
          have hjk := hJ.hjk
          simp only [vars_setVar, if_true, arrs_setVar, arrs_setArr] at hp ⊢
          rw [List.getElem?_set_ne (by omega)]
          exact hJ.hout p (by omega)
        · have := hJ.hjk; simp; omega
        · intro i hi
          simp only [bigBits_setVar, hbits]
          split
          · omega
          · exact hJ.hbit i hi
        · have hu := bval_update (b := bigBits D τ t) 0 hkD
          have hs := hJ.hsum
          rw [bigBits_setVar, hbits]
          simp only [vars_setVar, if_true, pow_succ]
          rw [hbit, hk] at *
          omega
        · simp only [vars_setVar, if_true, Cond.size, Expr.size, size_ixE]
          omega)
      h0
  obtain ⟨-, -, hget⟩ := hJ.evalB_bit hrep hx hB ht hD
  have hb0 : bigBits D τ t (τ.vars "bk") = 0 := by
    rw [evalB_condEq hget (evalB_lit (by omega))] at hf
    have := hJ.hbit _ (hJ.k_lt hx)
    simp at hf; omega
  exact ⟨τ, K, hr, hJ, hb0, by simpa [Cond.size, Expr.size] using hK⟩

/-- The final state of `addPow` represents `x + 2 ^ j`, whether or not the
length was raised. -/
theorem carry_rep {D t j x k : ℕ} {σ τ ρ : Env} (hrep : BigRep D σ t x)
    (hJ : CarryInv D t j x σ τ) (hx : x + 2 ^ j < 2 ^ D) (hk : τ.vars "bk" = k)
    (hb0 : bigBits D τ t k = 0)
    (hρb : ρ.arrs "xb" = (τ.arrs "xb").set (t * D + k) 1)
    (hρa : ∀ a, a ≠ "xb" → a ≠ "xt" → ρ.arrs a = σ.arrs a)
    (hρt : ∀ p, p ≠ t → (ρ.arrs "xt")[p]? = (σ.arrs "xt")[p]?)
    (hρlt : (ρ.arrs "xt").length = (σ.arrs "xt").length)
    (hρtop : bigTop ρ t = max (bigTop σ t) (k + 1))
    (hρi : ρ.inp = σ.inp) (hρo : ρ.out = σ.out) :
    BigRep D ρ t (x + 2 ^ j) ∧ BigFrame D t σ ρ := by
  have hkD : k < D := hk ▸ hJ.k_lt hx
  have hlen : t * D + k < (τ.arrs "xb").length := by
    rw [hJ.hlen]; have := hrep.lenb; omega
  have hbits := bigBits_of_set hρb hlen
  have hup : ∀ i, k ≤ i → bigBits D τ t i = bigBits D σ t i := fun i hi => by
    unfold bigBits; exact getD_congr (hJ.hout _ (Or.inr (by omega)))
  have hT := hrep.top_le
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨hρa, ?_, hρlt, ?_, hρt, hρi, hρo⟩⟩
  · rw [hρb, List.length_set, hJ.hlen]; exact hrep.lenb
  · rw [hρlt]; exact hrep.lent
  · intro i hi; simp only [hbits]; split
    · omega
    · exact hJ.hbit i hi
  · rw [hbits]
    have hu := bval_update (b := bigBits D τ t) 1 hkD
    have hs := hJ.hsum
    rw [hb0, hk] at *
    omega
  · rw [hρtop]; omega
  · intro i hi hiD
    rw [hρtop] at hi
    simp only [hbits]
    rw [if_neg (by omega), hup i (by omega)]
    exact hrep.zero i (by omega) hiD
  · intro _
    simp only [hρtop, hbits]
    by_cases hc : bigTop σ t ≤ k + 1
    · rw [max_eq_right hc, if_pos (by omega)]
    · rw [max_eq_left (by omega), if_neg (by omega), hup _ (by omega)]
      exact hrep.top_bit (by omega)
  · rw [hρb, List.length_set, hJ.hlen]
  · intro p hp
    have hjk := hJ.hjk
    rw [hρb, List.getElem?_set_ne (by omega)]
    exact hJ.hout p (by omega)

/-- **Adding a power of two.** Adding `2 ^ j` to the number `x` with
index `t` changes only its own bits and length and the scratch scalar
`bk`, and costs at most `20 · log₂ (x + 2 ^ j) + 30`. -/
theorem addPow_run {B D t j x : ℕ} {σ : Env} (hrep : BigRep D σ t x) (ht : σ.vars "bt" = t)
    (hjv : σ.vars "bj" = j) (hD : σ.vars "D" = D) (hj : j < D) (hx : x + 2 ^ j < 2 ^ D)
    (hB : t * D + D + 2 < B) :
    ∃ σ' K, Run B addPow σ σ' K ∧ BigRep D σ' t (x + 2 ^ j) ∧ BigFrame D t σ σ' ∧
      (∀ y, y ≠ "bk" → σ'.vars y = σ.vars y) ∧ K ≤ 20 * Nat.log 2 (x + 2 ^ j) + 30 := by
  have h0 : CarryInv D t j x σ (σ.setVar "bk" j) := by
    refine ⟨fun y hy => by simp [hy], fun a _ => rfl, rfl, rfl, rfl, fun p _ => rfl, by simp,
      fun i hi => hrep.bit_le i hi, ?_⟩
    simp [hrep.val]
  obtain ⟨τ, K1, hr1, hJ, hb0, hK1⟩ := addPowLoop_run hrep hx hB ht hD h0
  obtain ⟨k, hk⟩ : ∃ k, τ.vars "bk" = k := ⟨_, rfl⟩
  obtain ⟨hix, hlen, -⟩ := hJ.evalB_bit hrep hx hB ht hD
  have hkD := hJ.k_lt hx
  have hlog : k ≤ Nat.log 2 (x + 2 ^ j) := Nat.le_log_of_pow_le (by norm_num) (hk ▸ hJ.pow_le)
  rw [hk] at hix hlen hb0 hkD hK1
  simp only [vars_setVar, if_true] at hK1
  have htD : t ≤ t * D := Nat.le_mul_of_pos_right t (by omega)
  have hT := hrep.top_le
  have hxt : (τ.setArr "xb" (t * D + k) 1).arrs "xt" = σ.arrs "xt" := by
    simp [hJ.ha "xt" (by decide)]
  have hτ1t : (τ.setArr "xb" (t * D + k) 1).vars "bt" = t := by
    rw [vars_setArr, hJ.hv "bt" (by decide), ht]
  have hgt : (Expr.get "xt" (.var "bt")).evalB B (τ.setArr "xb" (t * D + k) 1) =
      some (bigTop σ t) :=
    evalB_get (evalB_var (by rw [hτ1t]; omega))
      (by rw [hτ1t, hxt]; exact getElem?_eq_some_getD hrep.lent) (by omega)
  have hk1 : (Expr.add (.var "bk") (.lit 1)).evalB B (τ.setArr "xb" (t * D + k) 1) =
      some (k + 1) := by simp [hk]; omega
  have hcond := evalB_condLt hgt hk1
  have hrs : Run B (.store "xb" (ixE "bt") (.lit 1)) τ (τ.setArr "xb" (t * D + k) 1) 7 :=
    (Run.store (a := "xb") (i := ixE "bt") (e := .lit 1) (idx := t * D + k) (v := 1) hix
      (evalB_lit (by omega)) hlen).mono (by simp)
  have hra : Run B (.assign "bk" (.var "bj")) σ (σ.setVar "bk" j) 2 :=
    (Run.assign (x := "bk") (e := .var "bj") (v := j) (by simp [hjv]; omega)).mono (by simp)
  have hvars : ∀ y, y ≠ "bk" → (τ.setArr "xb" (t * D + k) 1).vars y = σ.vars y := fun y hy => by
    simp [hJ.hv y hy]
  by_cases hc : bigTop σ t < k + 1
  · have hrt := Run.store (B := B) (σ := τ.setArr "xb" (t * D + k) 1) (a := "xt")
      (i := .var "bt") (e := .add (.var "bk") (.lit 1)) (idx := t) (v := k + 1)
      (by
        have := evalB_var (B := B) (x := "bt") (σ := τ.setArr "xb" (t * D + k) 1)
          (by rw [hτ1t]; omega)
        rwa [hτ1t] at this)
      hk1 (by simpa [hJ.ha "xt" (by decide)] using hrep.lent)
    obtain ⟨hR, hF⟩ := carry_rep (ρ := (τ.setArr "xb" (t * D + k) 1).setArr "xt" t (k + 1))
      hrep hJ hx hk hb0 (by simp) (fun a h1 h2 => by simp [h1, h2, hJ.ha a h1])
      (fun p hp => by
        simp only [arrs_setArr, if_true]
        rw [List.getElem?_set_ne (Ne.symm hp)]
        simpa using congrArg (·[p]?) hxt)
      (by simpa using congrArg List.length hxt)
      (by
        have hl : t < ((τ.setArr "xb" (t * D + k) 1).arrs "xt").length := by
          rw [hxt]; exact hrep.lent
        have : bigTop ((τ.setArr "xb" (t * D + k) 1).setArr "xt" t (k + 1)) t = k + 1 := by
          unfold bigTop; rw [arrs_setArr, if_pos rfl]; exact getD_set_self hl
        rw [this, max_eq_right (show bigTop σ t ≤ k + 1 by omega)])
      (by simp [hJ.hi]) (by simp [hJ.ho])
    refine ⟨_, _, Run.seq hra (Run.seq hr1 (Run.seq hrs (Run.ite_true
      (by rw [hcond]; simp [hc]) hrt))), hR, hF, fun y hy => by simpa using hvars y hy, ?_⟩
    simp only [Cond.size, Expr.size]
    omega
  · obtain ⟨hR, hF⟩ := carry_rep (ρ := τ.setArr "xb" (t * D + k) 1)
      hrep hJ hx hk hb0 (by simp) (fun a h1 h2 => by simp [h1, hJ.ha a h1])
      (fun p hp => by rw [hxt]) (congrArg List.length hxt)
      (by
        have : bigTop (τ.setArr "xb" (t * D + k) 1) t = bigTop σ t := by
          unfold bigTop; rw [hxt]
        rw [this, max_eq_left (show k + 1 ≤ bigTop σ t by omega)])
      (by simp [hJ.hi]) (by simp [hJ.ho])
    refine ⟨_, _, Run.seq hra (Run.seq hr1 (Run.seq hrs (Run.ite_false
      (by rw [hcond]; simp [hc]) Run.skip))), hR, hF, hvars, ?_⟩
    simp only [Cond.size, Expr.size]
    omega

/-! ### Comparing -/

/-- Scan the bits below `bk` from the top down for the first difference,
and leave in `blt` the bit of the second number there. -/
def cmpLoop : Com :=
  .while (.lt (.lit 0) (.var "bk"))
    (.seq (.assign "bk" (.sub (.var "bk") (.lit 1)))
      (.ite (.eq (.get "xb" (ixE "ca1")) (.get "xb" (ixE "ca2"))) .skip
        (.seq (.assign "blt" (.get "xb" (ixE "ca2"))) (.assign "bk" (.lit 0)))))

/-- Set `blt` to `1` if the number with index `ca1` is smaller than the
one with index `ca2`, else to `0`. -/
def bigCmp : Com :=
  .seq (.assign "blt" (ltX (.get "xt" (.var "ca1")) (.get "xt" (.var "ca2"))))
    (.ite (.eq (.get "xt" (.var "ca1")) (.get "xt" (.var "ca2")))
      (.seq (.assign "bk" (.get "xt" (.var "ca1"))) cmpLoop) .skip)

/-- The invariant of the comparison loop on two numbers of length `T`:
either no difference was found yet above `bk`, or the answer is in
`blt`. -/
structure CmpInv (D t1 t2 x1 x2 T : ℕ) (σ τ : Env) : Prop where
  hv : ∀ y, y ≠ "blt" → y ≠ "bk" → τ.vars y = σ.vars y
  ha : τ.arrs = σ.arrs
  hi : τ.inp = σ.inp
  ho : τ.out = σ.out
  hk : τ.vars "bk" ≤ T
  hst : (τ.vars "blt" = 0 ∧
      ∀ i, τ.vars "bk" ≤ i → i < T → bigBits D σ t1 i = bigBits D σ t2 i) ∨
    (τ.vars "bk" = 0 ∧ τ.vars "blt" = ind (x1 < x2))

theorem evalB_bitAt {B D t x i : ℕ} {a : String} {σ τ : Env} (hrep : BigRep D σ t x)
    (ha : τ.arrs = σ.arrs) (hv : τ.vars a = t) (hD : τ.vars "D" = D) (hk : τ.vars "bk" = i)
    (hi : i < D) (hB : t * D + D + 2 < B) (htB : t < B) :
    (Expr.get "xb" (ixE a)).evalB B τ = some (bigBits D σ t i) :=
  evalB_get (evalB_ixE hv hD hk htB (by omega) (by omega))
    (by rw [ha]; exact getElem?_eq_some_getD (by have := hrep.lenb; omega))
    (by have := hrep.bit_le i hi; omega)

theorem evalB_topAt {B D t x : ℕ} {a : String} {σ τ : Env} (hrep : BigRep D σ t x)
    (ha : τ.arrs = σ.arrs) (hv : τ.vars a = t) (htB : t < B) (hB : D < B) :
    (Expr.get "xt" (.var a)).evalB B τ = some (bigTop σ t) :=
  evalB_get (evalB_var (by rw [hv]; omega))
    (by rw [hv, ha]; exact getElem?_eq_some_getD hrep.lent)
    (by have := hrep.top_le; omega)

/-- Two numbers of the same length whose bits agree below it are equal. -/
theorem BigRep.eq_of_agree {D t1 t2 x1 x2 : ℕ} {σ : Env} (h1 : BigRep D σ t1 x1)
    (h2 : BigRep D σ t2 x2) (hT : bigTop σ t1 = bigTop σ t2)
    (hag : ∀ i < bigTop σ t1, bigBits D σ t1 i = bigBits D σ t2 i) : x1 = x2 := by
  rw [← h1.val, ← h2.val]
  refine bval_congr fun i hi => ?_
  by_cases hiT : i < bigTop σ t1
  · exact hag i hiT
  · rw [h1.zero i (by omega) hi, h2.zero i (by omega) hi]

/-- **The comparison loop.** -/
theorem cmpLoop_run {B D t1 t2 x1 x2 : ℕ} {σ : Env} (h1 : BigRep D σ t1 x1)
    (h2 : BigRep D σ t2 x2) (hT : bigTop σ t1 = bigTop σ t2) (ht1 : σ.vars "ca1" = t1)
    (ht2 : σ.vars "ca2" = t2) (hD : σ.vars "D" = D) (hB1 : t1 * D + D + 2 < B)
    (hB2 : t2 * D + D + 2 < B) (ht1B : t1 < B) (ht2B : t2 < B) {τ0 : Env}
    (h0 : CmpInv D t1 t2 x1 x2 (bigTop σ t1) σ τ0) :
    ∃ τ K, Run B cmpLoop τ0 τ K ∧ CmpInv D t1 t2 x1 x2 (bigTop σ t1) σ τ ∧
      τ.vars "bk" = 0 ∧ K ≤ 40 * τ0.vars "bk" + 4 := by
  have hTD := h1.top_le
  obtain ⟨τ, K, hr, hJ, hf, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.lit 0) (.var "bk"))
      (c := .seq (.assign "bk" (.sub (.var "bk") (.lit 1)))
        (.ite (.eq (.get "xb" (ixE "ca1")) (.get "xb" (ixE "ca2"))) .skip
          (.seq (.assign "blt" (.get "xb" (ixE "ca2"))) (.assign "bk" (.lit 0)))))
      (CmpInv D t1 t2 x1 x2 (bigTop σ t1) σ) (fun τ => 40 * τ.vars "bk")
      (fun τ hJ => ⟨_, evalB_condLt (evalB_lit (by omega))
        (evalB_var (by have := hJ.hk; omega))⟩)
      (by
        intro τ hJ hc
        obtain ⟨k, hk⟩ : ∃ k, τ.vars "bk" = k := ⟨_, rfl⟩
        have hkT : k ≤ bigTop σ t1 := hk ▸ hJ.hk
        have hk0 : 0 < k := by
          rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by rw [hk]; omega))] at hc
          simpa [hk] using hc
        have hst : τ.vars "blt" = 0 ∧
            ∀ i, k ≤ i → i < bigTop σ t1 → bigBits D σ t1 i = bigBits D σ t2 i := by
          rcases hJ.hst with h | h
          · rw [hk] at h; exact h
          · omega
        have hv1 : ∀ y, y ≠ "blt" → y ≠ "bk" → (τ.setVar "bk" (k - 1)).vars y = σ.vars y :=
          fun y hy1 hy2 => by simp [hy2, hJ.hv y hy1 hy2]
        have e1 := evalB_bitAt (B := B) (i := k - 1) (a := "ca1")
          (τ := τ.setVar "bk" (k - 1)) h1 hJ.ha
          (by rw [hv1 _ (by decide) (by decide), ht1]) (by rw [hv1 _ (by decide) (by decide), hD])
          (by simp) (by omega) hB1 ht1B
        have e2 := evalB_bitAt (B := B) (i := k - 1) (a := "ca2")
          (τ := τ.setVar "bk" (k - 1)) h2 hJ.ha
          (by rw [hv1 _ (by decide) (by decide), ht2]) (by rw [hv1 _ (by decide) (by decide), hD])
          (by simp) (by omega) hB2 ht2B
        have hra : Run B (.assign "bk" (.sub (.var "bk") (.lit 1))) τ (τ.setVar "bk" (k - 1)) 4 :=
          (Run.assign (x := "bk") (e := .sub (.var "bk") (.lit 1)) (v := k - 1)
            (by simp [hk]; omega)).mono (by simp)
        by_cases heq : bigBits D σ t1 (k - 1) = bigBits D σ t2 (k - 1)
        · refine ⟨τ.setVar "bk" (k - 1), _, Run.seq hra (Run.ite_true
            (by rw [evalB_condEq e1 e2]; simp [heq]) Run.skip),
            ⟨hv1, hJ.ha, hJ.hi, hJ.ho, by simp; omega, Or.inl ⟨by simp [hst.1], ?_⟩⟩, ?_⟩
          · intro i hi1 hi2
            simp only [vars_setVar, if_true] at hi1
            by_cases hik : i = k - 1
            · rw [hik]; exact heq
            · exact hst.2 i (by omega) hi2
          · simp only [Cond.size, Expr.size, size_ixE, hk, vars_setVar, if_true]
            omega
        · have hag : ∀ i, k - 1 < i → i < D → bigBits D σ t1 i = bigBits D σ t2 i :=
            fun i hi1 hi2 => by
              by_cases hiT : i < bigTop σ t1
              · exact hst.2 i (by omega) hiT
              · rw [h1.zero i (by omega) hi2, h2.zero i (by omega) hi2]
          have hind := ind_lt_of_diff h1.bit_le h2.bit_le (by omega) heq hag
          rw [h1.val, h2.val] at hind
          refine ⟨((τ.setVar "bk" (k - 1)).setVar "blt" (bigBits D σ t2 (k - 1))).setVar "bk" 0, _,
            Run.seq hra (Run.ite_false (by rw [evalB_condEq e1 e2]; simp [heq])
              (Run.seq (Run.assign (x := "blt") (e := .get "xb" (ixE "ca2"))
                (v := bigBits D σ t2 (k - 1)) e2)
                (Run.assign (x := "bk") (e := .lit 0) (v := 0) (evalB_lit (by omega))))),
            ⟨fun y hy1 hy2 => by simp [hy1, hy2, hJ.hv y hy1 hy2], hJ.ha, hJ.hi, hJ.ho,
              by simp, Or.inr ⟨by simp, by simp [hind]⟩⟩, ?_⟩
          simp only [Cond.size, Expr.size, size_ixE, hk, vars_setVar, if_true]
          omega)
      h0
  have hk0 : τ.vars "bk" = 0 := by
    rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by have := hJ.hk; omega))] at hf
    simp at hf; omega
  refine ⟨τ, K, hr, hJ, hk0, ?_⟩
  simp only [Cond.size, Expr.size] at hK
  omega

/-- **Comparing two numbers.** The scalar `blt` becomes `1` if the number
with index `t1` is smaller than the one with index `t2`, else `0`, at a
cost of at most `40 · log₂ x1 + 70`. -/
theorem bigCmp_run {B D t1 t2 x1 x2 : ℕ} {σ : Env} (h1 : BigRep D σ t1 x1)
    (h2 : BigRep D σ t2 x2) (ht1 : σ.vars "ca1" = t1) (ht2 : σ.vars "ca2" = t2)
    (hD : σ.vars "D" = D) (hB1 : t1 * D + D + 2 < B) (hB2 : t2 * D + D + 2 < B)
    (ht1B : t1 < B) (ht2B : t2 < B) :
    ∃ σ' K, Run B bigCmp σ σ' K ∧ σ'.vars "blt" = ind (x1 < x2) ∧
      (∀ y, y ≠ "blt" → y ≠ "bk" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out ∧ K ≤ 40 * Nat.log 2 x1 + 70 := by
  have hT1 := h1.top_le
  have hT2 := h2.top_le
  have hlog := h1.top_le_log
  have g1 := evalB_topAt (B := B) (a := "ca1") (τ := σ) h1 rfl ht1 ht1B (by omega)
  have g2 := evalB_topAt (B := B) (a := "ca2") (τ := σ) h2 rfl ht2 ht2B (by omega)
  have hlt := evalB_ltX g1 g2 (by omega) (by omega) (by omega)
  have g1' := evalB_topAt (B := B) (a := "ca1")
    (τ := σ.setVar "blt" (ind (bigTop σ t1 < bigTop σ t2))) h1
    rfl (by simp [ht1]) ht1B (by omega)
  have g2' := evalB_topAt (B := B) (a := "ca2")
    (τ := σ.setVar "blt" (ind (bigTop σ t1 < bigTop σ t2))) h2
    rfl (by simp [ht2]) ht2B (by omega)
  have hra := Run.assign (x := "blt") (e := ltX (.get "xt" (.var "ca1")) (.get "xt" (.var "ca2")))
    hlt
  by_cases hTe : bigTop σ t1 = bigTop σ t2
  · have h0 : CmpInv D t1 t2 x1 x2 (bigTop σ t1) σ
        ((σ.setVar "blt" (ind (bigTop σ t1 < bigTop σ t2))).setVar "bk" (bigTop σ t1)) :=
      ⟨fun y hy1 hy2 => by simp [hy1, hy2], rfl, rfl, rfl, by simp,
        Or.inl ⟨by simp [hTe, ind], fun i hi1 hi2 => by simp at hi1; omega⟩⟩
    obtain ⟨τ, K, hr, hJ, hk0, hK⟩ := cmpLoop_run h1 h2 hTe ht1 ht2 hD hB1 hB2 ht1B ht2B h0
    have hblt : τ.vars "blt" = ind (x1 < x2) := by
      rcases hJ.hst with ⟨hb, hag⟩ | ⟨_, hb⟩
      · have := h1.eq_of_agree h2 hTe (fun i hi => hag i (by omega) hi)
        rw [hb, this]; simp [ind]
      · exact hb
    refine ⟨τ, _, Run.seq hra (Run.ite_true (by rw [evalB_condEq g1' g2']; simp [hTe])
      (Run.seq (Run.assign (x := "bk") (e := .get "xt" (.var "ca1")) (v := bigTop σ t1) g1') hr)),
      hblt, fun y hy1 hy2 => hJ.hv y hy1 hy2, hJ.ha, hJ.hi, hJ.ho, ?_⟩
    simp only [vars_setVar, if_true] at hK
    simp only [Cond.size, Expr.size, size_ltX]
    omega
  · have hind : ind (bigTop σ t1 < bigTop σ t2) = ind (x1 < x2) := by
      rw [ind_eq_iff]
      constructor
      · exact h1.lt_of_top_lt h2
      · intro hx
        by_contra hc
        have := h2.lt_of_top_lt h1 (by omega)
        omega
    refine ⟨_, _, Run.seq hra (Run.ite_false (by rw [evalB_condEq g1' g2']; simp [hTe])
      Run.skip), by simp [hind], fun y hy1 hy2 => by simp [hy1], rfl, rfl, rfl, ?_⟩
    simp only [Cond.size, Expr.size, size_ltX]
    omega

end Lax185574Proofs.Chain.Ram
